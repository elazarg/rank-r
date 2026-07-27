"""Exact nonlinear-real checks for same-support barrier inequalities.

The Z3 `qfnra-nlsat` procedure works over exact rational polynomials.  A query
asks whether there are two consecutive one-shot Nash supports, backed by a
continuation payoff in the convex hull of the 15 terminal outcomes, that
violate a proposed telescoping inequality.  `unsat` is therefore an exact
certificate for this semialgebraic formulation; `sat` returns an algebraic
counter-witness; `unknown` proves nothing.

CAVEAT for `--reduce-triple`: the reduction solves each recurrence equation for
one quitting-odds variable and therefore constrains every elimination
denominator to be nonzero.  An `unsat` under `--reduce-triple` consequently
certifies the barrier only *away from the denominator variety*: candidate
solutions at which a solved odds expression degenerates are excluded from the
search rather than refuted.  The branch choice `sp.solve(...)[0]` is not itself
a restriction -- each equation is bilinear, hence linear in the solved odd, so
the solution is unique -- but the nonzero side-condition does narrow what
`unsat` means.  The unreduced path carries no such caveat.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from math import gcd, lcm
import itertools
import json
from pathlib import Path

import numpy as np
from scipy.spatial import ConvexHull
import sympy as sp
import z3


WEIGHTS = {
    1: (-1, -1, 0, -1),
    2: (1, 1, -1, -1),
    3: (1, -1, 0, -1),
    6: (Fraction(3, 4), 1, -1, 1),
    # The earlier (-1,1,1,-1) candidate is exactly false; this replacement is
    # numerically promising but not yet certified.
    7: (Fraction(3, 4), 1, 1, 1),
    9: (1, -1, 0, -1),
    13: (1, -1, 1, 1),
    14: (1, 1, -1, 1),
}


def rat(value: Fraction | int | float | str):
    q = value if isinstance(value, Fraction) else Fraction(str(value))
    return z3.RealVal(f"{q.numerator}/{q.denominator}")


def bit(mask: int, i: int) -> bool:
    return bool(mask & (1 << i))


def action_probability(mask: int, p):
    value = rat(1)
    for i, pi in enumerate(p):
        value *= pi if bit(mask, i) else 1 - pi
    return value


def phase_data(payoff, p):
    immediate = []
    for i in range(4):
        immediate.append(sum(
            (action_probability(mask, p) * payoff[mask][i]
             for mask in range(1, 16)),
            rat(0),
        ))
    stay = z3.Product([1 - pi for pi in p])
    return immediate, stay


def action_difference(payoff, continuation, p, player: int):
    no_opp = z3.Product([1 - p[j] for j in range(4) if j != player])
    quit_value = rat(0)
    continue_absorb = rat(0)
    for opp_mask in range(16):
        if bit(opp_mask, player):
            continue
        probability = rat(1)
        for j in range(4):
            if j == player:
                continue
            probability *= p[j] if bit(opp_mask, j) else 1 - p[j]
        quit_value += probability * payoff[opp_mask | (1 << player)][player]
        if opp_mask:
            continue_absorb += probability * payoff[opp_mask][player]
    return quit_value - continue_absorb - no_opp * continuation[player]


def indifference_threshold(payoff, p, player: int):
    """Continuation coordinate making `player` indifferent at action `p`."""
    no_opp = z3.Product([1 - p[j] for j in range(4) if j != player])
    quit_value = rat(0)
    continue_absorb = rat(0)
    for opp_mask in range(16):
        if bit(opp_mask, player):
            continue
        probability = rat(1)
        for j in range(4):
            if j == player:
                continue
            probability *= p[j] if bit(opp_mask, j) else 1 - p[j]
        quit_value += probability * payoff[opp_mask | (1 << player)][player]
        if opp_mask:
            continue_absorb += probability * payoff[opp_mask][player]
    return (quit_value - continue_absorb) / no_opp


def indifference_threshold_odds(payoff, odds, player: int):
    """Indifference threshold as a polynomial in opponent quitting odds."""
    quit_value = rat(0)
    continue_absorb = rat(0)
    for opponent_mask in range(16):
        if bit(opponent_mask, player):
            continue
        likelihood_ratio = rat(1)
        for j in range(4):
            if j != player and bit(opponent_mask, j):
                likelihood_ratio *= odds[j]
        quit_value += (
            likelihood_ratio * payoff[opponent_mask | (1 << player)][player]
        )
        if opponent_mask:
            continue_absorb += likelihood_ratio * payoff[opponent_mask][player]
    return quit_value - continue_absorb


def constrain_support(solver, payoff, continuation, p, mask: int):
    for i, pi in enumerate(p):
        if bit(mask, i):
            solver.add(pi > 0, pi < 1)
        else:
            solver.add(pi == 0)
        difference = action_difference(payoff, continuation, p, i)
        solver.add(difference == 0 if bit(mask, i) else difference <= 0)


def decimal(model, expression) -> str:
    return model.eval(expression, model_completion=True).as_decimal(18)


def exact(model, expression) -> str:
    return str(model.eval(expression, model_completion=True))


def primitive(values: list[Fraction]) -> tuple[int, ...]:
    denominator = 1
    for value in values:
        denominator = lcm(denominator, value.denominator)
    integers = [value.numerator * (denominator // value.denominator) for value in values]
    divisor = 0
    for value in integers:
        divisor = gcd(divisor, abs(value))
    return tuple(value // max(1, divisor) for value in integers)


def convex_hull_facets(points: list[list[Fraction]]) -> list[tuple[int, ...]]:
    """Exact primitive inequalities ``a*x <= b`` from Qhull facet incidences."""
    hull = ConvexHull(np.asarray([[float(x) for x in row] for row in points]))
    facets: set[tuple[int, ...]] = set()
    for simplex in hull.simplices:
        base = points[int(simplex[0])]
        differences = [
            [points[int(index)][j] - base[j] for j in range(4)]
            for index in simplex[1:]
        ]
        matrix = sp.Matrix([[sp.Rational(x.numerator, x.denominator) for x in row]
                            for row in differences])
        nullspace = matrix.nullspace()
        if len(nullspace) != 1:
            raise RuntimeError(f"degenerate facet simplex {simplex}")
        normal = [Fraction(int(x.p), int(x.q)) for x in nullspace[0]]
        offset = sum((normal[j] * base[j] for j in range(4)), Fraction(0))
        values = [sum((normal[j] * point[j] for j in range(4)), Fraction(0)) - offset
                  for point in points]
        if all(value <= 0 for value in values):
            oriented = normal + [offset]
        elif all(value >= 0 for value in values):
            oriented = [-value for value in normal] + [-offset]
        else:
            raise RuntimeError(f"inexact Qhull facet incidence {simplex}: {values}")
        facets.add(primitive(oriented))
    return sorted(facets)


def sym_probability(mask: int, p):
    value = sp.Integer(1)
    for i, pi in enumerate(p):
        value *= pi if bit(mask, i) else 1 - pi
    return sp.expand(value)


def sym_threshold(payoff, p, player: int):
    no_opp = sp.prod(1 - p[j] for j in range(4) if j != player)
    quit_value = sp.Integer(0)
    continue_absorb = sp.Integer(0)
    for opp_mask in range(16):
        if bit(opp_mask, player):
            continue
        probability = sp.Integer(1)
        for j in range(4):
            if j == player:
                continue
            probability *= p[j] if bit(opp_mask, j) else 1 - p[j]
        quit_value += probability * payoff[opp_mask | (1 << player)][player]
        if opp_mask:
            continue_absorb += probability * payoff[opp_mask][player]
    return sp.factor((quit_value - continue_absorb) / no_opp)


def sympy_to_z3(expression, symbol_map):
    """Translate the rational Sympy fragment used by the recurrence reduction."""
    expression = sp.sympify(expression)
    if expression.is_Integer:
        return rat(int(expression))
    if expression.is_Rational:
        return rat(Fraction(int(expression.p), int(expression.q)))
    if expression.is_Symbol:
        return symbol_map[expression]
    if expression.is_Add:
        return sum((sympy_to_z3(arg, symbol_map) for arg in expression.args), rat(0))
    if expression.is_Mul:
        return z3.Product([sympy_to_z3(arg, symbol_map) for arg in expression.args])
    if expression.is_Pow and expression.exp.is_Integer:
        return sympy_to_z3(expression.base, symbol_map) ** int(expression.exp)
    raise TypeError(f"unsupported Sympy expression: {expression!r}")


def reduced_triple_recurrence(payoff_fractions, mask: int, p_z3):
    """Parametrize the three predecessor odds by one positive root.

    Each active indifference equation omits that player's own predecessor
    probability.  In odds coordinates it is bilinear in the other two odds.
    Two equations therefore solve linearly for two odds, leaving one exact
    polynomial equation in the current action and a single predecessor odd.
    """
    schemes = {
        # mask: (free odd, [(equation player, solved odd), ...], residual equation)
        7: (1, ((0, 2), (2, 0)), 1),
        13: (2, ((0, 3), (3, 0)), 2),
        14: (3, ((1, 2), (2, 1)), 3),
    }
    if mask not in schemes:
        raise ValueError("--reduce-triple is implemented for supports 7, 13, 14")

    payoff = [
        [sp.Rational(value.numerator, value.denominator) for value in row]
        for row in payoff_fractions
    ]
    ps = sp.symbols("rp0:4")
    vs = sp.symbols("rv0:4")
    p = [ps[i] if bit(mask, i) else sp.Integer(0) for i in range(4)]
    q = [vs[i] / (1 + vs[i]) if bit(mask, i) else sp.Integer(0)
         for i in range(4)]
    stay = sp.prod(1 - value for value in p)
    immediate = [
        sp.expand(sum(
            sym_probability(outcome, p) * payoff[outcome][i]
            for outcome in range(1, 16)
        ))
        for i in range(4)
    ]
    equations = {
        i: sp.factor(sp.fraction(sp.together(
            sym_threshold(payoff, q, i)
            - (immediate[i] + stay * sym_threshold(payoff, p, i))
        ))[0])
        for i in range(4) if bit(mask, i)
    }

    free_index, solve_order, residual_index = schemes[mask]
    substitutions = {}
    denominators = []
    for equation_index, variable_index in solve_order:
        equation = sp.factor(equations[equation_index].subs(substitutions))
        solution = sp.factor(sp.solve(equation, vs[variable_index])[0])
        substitutions[vs[variable_index]] = solution
        denominators.append(sp.factor(sp.fraction(solution)[1]))
    residual = sp.factor(sp.fraction(sp.together(
        equations[residual_index].subs(substitutions)
    ))[0])

    root = z3.Real("previous_root_odd")
    symbol_map = {ps[i]: p_z3[i] for i in range(4)}
    symbol_map[vs[free_index]] = root
    odds = [rat(0) for _ in range(4)]
    odds[free_index] = root
    for variable, expression in substitutions.items():
        odds[int(str(variable)[2:])] = sympy_to_z3(expression, symbol_map)
    q_z3 = [odds[i] / (1 + odds[i]) if bit(mask, i) else rat(0)
            for i in range(4)]
    residual_z3 = sympy_to_z3(residual, symbol_map)
    denominator_z3 = [sympy_to_z3(value, symbol_map) for value in denominators]
    return q_z3, odds, root, free_index, residual_z3, denominator_z3


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("mask", type=int, choices=range(1, 15))
    parser.add_argument("--previous-mask", type=int, choices=range(1, 15))
    parser.add_argument("--feasible-only", action="store_true")
    parser.add_argument("--min-hazard", default="0")
    parser.add_argument("--margin", default="1")
    parser.add_argument("--weight", help="four comma-separated rational coefficients")
    parser.add_argument("--timeout-ms", type=int, default=180000)
    parser.add_argument("--lambda", dest="use_lambda", action="store_true")
    parser.add_argument("--substitute-active", action="store_true")
    parser.add_argument(
        "--eliminate-inactive",
        action="store_true",
        help=(
            "for a three-player same-support query, eliminate the sole inactive "
            "continuation coordinate by exact lower/upper-bound comparisons"
        ),
    )
    parser.add_argument(
        "--reduce-triple",
        action="store_true",
        help="reduce a 7/13/14 same-support recurrence to three p variables and one root",
    )
    parser.add_argument("--split", type=int, default=1)
    parser.add_argument(
        "--base-split",
        type=int,
        default=1,
        help="denominator of an optional coarse probability box to refine",
    )
    parser.add_argument(
        "--base-box",
        help="comma-separated coarse box indices, in displayed active-variable order",
    )
    parser.add_argument("--box-timeout-ms", type=int, default=10000)
    args = parser.parse_args()

    record = json.loads(
        Path(__file__).with_name("vary-singleton-survivors.json").read_text()
    )[0]
    payoff_fractions = [[Fraction(0) for _ in range(4)] for _ in range(16)]
    for mask, row in record["terminal"].items():
        payoff_fractions[int(mask)] = [Fraction(str(value)) for value in row]
    payoff = [[rat(value) for value in row] for row in payoff_fractions]

    p = [z3.Real(f"p{i}") for i in range(4)]
    q = [z3.Real(f"q{i}") for i in range(4)]
    lam = [z3.Real(f"lam{mask}") for mask in range(1, 16)]

    solver = z3.Tactic("qfnra-nlsat").solver()
    solver.set(timeout=args.timeout_ms)
    eliminate_inactive = args.eliminate_inactive
    if eliminate_inactive:
        if args.use_lambda or not args.substitute_active:
            raise ValueError("--eliminate-inactive requires --substitute-active without --lambda")
        if args.previous_mask not in (None, args.mask):
            raise ValueError("--eliminate-inactive currently handles same-support queries only")
        if sum(bit(args.mask, i) for i in range(4)) != 3:
            raise ValueError("--eliminate-inactive requires a three-player support")
    if args.reduce_triple:
        if args.use_lambda or not args.substitute_active:
            raise ValueError("--reduce-triple requires --substitute-active without --lambda")
        if args.previous_mask not in (None, args.mask):
            raise ValueError("--reduce-triple currently handles same-support queries only")
        if sum(bit(args.mask, i) for i in range(4)) != 3:
            raise ValueError("--reduce-triple requires a three-player support")
        (q, predecessor_odds, predecessor_root, predecessor_free_index,
         recurrence_residual, recurrence_denominators) = (
            reduced_triple_recurrence(payoff_fractions, args.mask, p)
        )

    facets = convex_hull_facets(payoff_fractions[1:])
    if args.use_lambda:
        continuation = [sum(
            (lam[mask - 1] * payoff[mask][i] for mask in range(1, 16)),
            rat(0),
        ) for i in range(4)]
        solver.add(sum(lam, rat(0)) == 1)
        solver.add(*[value >= 0 for value in lam])
    else:
        free_continuation = [z3.Real(f"y{i}") for i in range(4)]
        continuation = [
            indifference_threshold(payoff, p, i)
            if args.substitute_active and bit(args.mask, i)
            else free_continuation[i]
            for i in range(4)
        ]
        print(f"exact convex-hull facets={len(facets)}", flush=True)
        if not eliminate_inactive:
            for facet in facets:
                solver.add(sum((rat(facet[i]) * continuation[i] for i in range(4)), rat(0))
                           <= rat(facet[4]))
    if not eliminate_inactive and not args.reduce_triple:
        constrain_support(solver, payoff, continuation, p, args.mask)

    immediate, stay = phase_data(payoff, p)
    current = [immediate[i] + stay * continuation[i] for i in range(4)]
    previous_mask = args.previous_mask or args.mask
    if not eliminate_inactive and not args.reduce_triple:
        constrain_support(solver, payoff, current, q, previous_mask)

    hazard = 1 - stay
    solver.add(hazard >= rat(Fraction(args.min_hazard)))
    drop = rat(0)
    selected_weight = None
    if not args.feasible_only:
        if args.mask not in WEIGHTS and not args.weight:
            raise ValueError("a barrier --weight is required for this support")
        selected_weight = (
            tuple(Fraction(value.strip()) for value in args.weight.split(","))
            if args.weight else WEIGHTS[args.mask]
        )
        if len(selected_weight) != 4:
            raise ValueError("--weight requires four coefficients")
        weight = [rat(value) for value in selected_weight]
        drop = sum(
            (weight[i] * (current[i] - continuation[i]) for i in range(4)),
            rat(0),
        )
        margin = rat(Fraction(args.margin))
        if not eliminate_inactive:
            solver.add(drop < margin * hazard)

    if eliminate_inactive:
        inactive = next(i for i in range(4) if not bit(args.mask, i))
        active = [i for i in range(4) if bit(args.mask, i)]
        for i in range(4):
            if i in active:
                solver.add(p[i] > 0, p[i] < 1)
                if args.reduce_triple:
                    solver.add(predecessor_odds[i] > 0)
                else:
                    solver.add(q[i] > 0, q[i] < 1)
            else:
                solver.add(p[i] == 0)
                if not args.reduce_triple:
                    solver.add(q[i] == 0)

        # The active current-support conditions hold definitionally because
        # their continuation coordinates are their indifference thresholds.
        # The active predecessor conditions are the three recurrence equations.
        if args.reduce_triple:
            solver.add(recurrence_residual == 0)
            solver.add(*[value != 0 for value in recurrence_denominators])
        else:
            for i in active:
                solver.add(action_difference(payoff, current, q, i) == 0)

        lower_bounds = [indifference_threshold(payoff, p, inactive)]
        predecessor_inactive_threshold = (
            indifference_threshold_odds(payoff, predecessor_odds, inactive)
            if args.reduce_triple
            else indifference_threshold(payoff, q, inactive)
        )
        lower_bounds.append(
            (predecessor_inactive_threshold - immediate[inactive]) / stay
        )
        upper_bounds = []
        for facet in facets:
            coefficient = facet[inactive]
            remainder = rat(facet[4]) - sum(
                (rat(facet[i]) * continuation[i] for i in active), rat(0)
            )
            if coefficient > 0:
                upper_bounds.append(remainder / rat(coefficient))
            elif coefficient < 0:
                lower_bounds.append(remainder / rat(coefficient))
            else:
                solver.add(remainder >= 0)

        # A common inactive continuation exists exactly when every lower bound
        # is below every upper bound.  The barrier violation supplies one
        # additional strict upper or lower bound.
        for lower in lower_bounds:
            for upper in upper_bounds:
                solver.add(lower <= upper)

        if not args.feasible_only:
            assert selected_weight is not None
            active_drop = sum(
                (rat(selected_weight[i]) * (current[i] - continuation[i])
                 for i in active),
                rat(0),
            )
            inactive_weight = Fraction(selected_weight[inactive])
            if inactive_weight == -1:
                barrier_upper = (
                    margin * hazard - active_drop + immediate[inactive]
                ) / hazard
                for lower in lower_bounds:
                    solver.add(lower < barrier_upper)
            elif inactive_weight == 1:
                barrier_lower = (
                    active_drop + immediate[inactive] - margin * hazard
                ) / hazard
                for upper in upper_bounds:
                    solver.add(barrier_lower < upper)
            else:
                raise ValueError(
                    "--eliminate-inactive currently requires inactive weight +/-1"
                )

    if args.reduce_triple and not eliminate_inactive:
        inactive = next(i for i in range(4) if not bit(args.mask, i))
        active = [i for i in range(4) if bit(args.mask, i)]
        for i in range(4):
            if i in active:
                solver.add(p[i] > 0, p[i] < 1, predecessor_odds[i] > 0)
            else:
                solver.add(p[i] == 0)
        solver.add(recurrence_residual == 0)
        solver.add(*[value != 0 for value in recurrence_denominators])
        # The inactive player must prefer continuing in both consecutive
        # phases.  The predecessor threshold is polynomial in quitting odds.
        solver.add(
            continuation[inactive]
            >= indifference_threshold(payoff, p, inactive)
        )
        solver.add(
            current[inactive]
            >= indifference_threshold_odds(payoff, predecessor_odds, inactive)
        )

    model = None
    if args.split <= 1:
        result = solver.check()
        if result == z3.sat:
            model = solver.model()
    else:
        active_variables = [
            (p[i], False) for i in range(4) if bit(args.mask, i)
        ]
        if args.reduce_triple:
            active_variables.append((predecessor_root, True))
        else:
            active_variables += [
                (q[i], False) for i in range(4) if bit(previous_mask, i)
            ]
        unknown_boxes = []
        result = z3.unsat
        base_indices = (
            tuple(int(value.strip()) for value in args.base_box.split(","))
            if args.base_box else tuple(0 for _ in active_variables)
        )
        if len(base_indices) != len(active_variables):
            raise ValueError(
                f"--base-box needs {len(active_variables)} indices, got {len(base_indices)}"
            )
        if args.base_split < 1 or any(
            value < 0 or value >= args.base_split for value in base_indices
        ):
            raise ValueError("invalid --base-split/--base-box probability cell")
        total = args.split ** len(active_variables)
        for box_index, indices in enumerate(
            itertools.product(range(args.split), repeat=len(active_variables)), 1
        ):
            solver.push()
            solver.set(timeout=args.box_timeout_ms)
            for ((variable, is_odd), base_index, index) in zip(
                active_variables, base_indices, indices
            ):
                denominator = args.base_split * args.split
                lower_index = base_index * args.split + index
                upper_index = lower_index + 1
                if is_odd:
                    # q in [a/n,b/n] iff odds q/(1-q) lies in
                    # [a/(n-a),b/(n-b)]; the last upper bound is +inf.
                    solver.add(variable >= rat(Fraction(
                        lower_index, denominator - lower_index
                    )))
                    if upper_index < denominator:
                        solver.add(variable <= rat(Fraction(
                            upper_index, denominator - upper_index
                        )))
                else:
                    solver.add(variable >= rat(Fraction(lower_index, denominator)))
                    solver.add(variable <= rat(Fraction(upper_index, denominator)))
            box_result = solver.check()
            if box_result == z3.sat:
                result = z3.sat
                model = solver.model()
                print(f"sat box {indices} ({box_index}/{total})", flush=True)
                solver.pop()
                break
            if box_result == z3.unknown:
                unknown_boxes.append(indices)
            solver.pop()
            if box_index % 25 == 0:
                print(
                    f"boxes {box_index}/{total}, unknown={len(unknown_boxes)}",
                    flush=True,
                )
        else:
            if unknown_boxes:
                result = z3.unknown
                print(f"unknown boxes ({len(unknown_boxes)}): {unknown_boxes}")
    print(
        f"support={args.mask} previous={previous_mask} "
        f"query={'feasible' if args.feasible_only else 'barrier'} result={result}"
    )
    if result == z3.sat:
        assert model is not None
        print("p", [decimal(model, value) for value in p])
        print("q", [decimal(model, value) for value in q])
        print("p exact", [exact(model, value) for value in p])
        print("q exact", [exact(model, value) for value in q])
        if eliminate_inactive:
            print("y(active)", {
                i: decimal(model, continuation[i])
                for i in range(4) if bit(args.mask, i)
            })
            print("y(active) exact", {
                i: exact(model, continuation[i])
                for i in range(4) if bit(args.mask, i)
            })
        else:
            print("y", [decimal(model, value) for value in continuation])
        if eliminate_inactive:
            print("inactive lower bounds", [decimal(model, value) for value in lower_bounds])
            print("inactive upper bounds", [decimal(model, value) for value in upper_bounds])
            print("inactive lower exact", [exact(model, value) for value in lower_bounds])
            if not args.feasible_only:
                if inactive_weight == -1:
                    print("barrier upper", decimal(model, barrier_upper))
                else:
                    print("barrier lower", decimal(model, barrier_lower))
        print("hazard", decimal(model, hazard))
        if not args.feasible_only:
            print("drop", decimal(model, drop))
            print("ratio", decimal(model, drop / hazard))
        if args.use_lambda:
            active_lam = [
                (mask, decimal(model, lam[mask - 1]))
                for mask in range(1, 16)
                if not z3.is_true(
                    z3.simplify(model.eval(lam[mask - 1], model_completion=True) == 0)
                )
            ]
            print("lambda", active_lam)


if __name__ == "__main__":
    main()
