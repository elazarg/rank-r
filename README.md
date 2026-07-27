# A machine-checked rank-$r$ partial-trace inequality

A Lean 4 formalization of the main theorem of `paper/rank-r.tex`,

> **Theorem 1.1.** Let $U, V$ be finite-dimensional complex Hilbert spaces and
> let $C \in \mathcal L(U \otimes V)$ have $\operatorname{rank} C \le r$. Then
> $$\|\mathrm{Tr}_U C\|_2^2 + \|\mathrm{Tr}_V C\|_2^2 \;\le\; r\|C\|_2^2 + \tfrac1r|\mathrm{Tr}\,C|^2 .$$

The manuscript's abstract records that these proofs are machine-checked. That
claim is deliberately narrow, and what follows spells out its limits.

## What is proved, and what it rests on

```lean
theorem RankR.rank_r_partial_trace_of_FGP_square
    (hU : Fintype.card U ≤ d) (hV : Fintype.card V ≤ d)
    (hFGP : FGPBound (Fin d) (Fin d))
    (C : Matrix (U × V) (U × V) ℂ) (r : ℕ) (hr : 0 < r) (hrank : C.rank ≤ r) :
    hsNormSq (ptraceU C) + hsNormSq (ptraceV C)
      ≤ r * hsNormSq C + (1 / r : ℝ) * Complex.normSq C.trace
```

`#print axioms RankR.rank_r_partial_trace_of_FGP_square` reports only
`propext, Classical.choice, Quot.sound`, and no declaration uses `sorry`,
`axiom`, `native_decide` or `set_option`. The axiom half of that claim is not
merely asserted: `RankR/Axioms.lean` wraps `#print axioms` in `#guard_msgs`
for each headline theorem, so the build fails if it ever stops holding.

The sole hypothesis is `FGPBound (Fin d) (Fin d)`: the double-antisymmetric
projection estimate of Fu–Gao–Park [arXiv:2607.21367] on $(\mathbb C^d)^{\otimes4}$,
all four tensor factors the same space, which is the form they state. It is
carried as a hypothesis rather than an `axiom` precisely so that
`#print axioms` stays meaningful and the dependency is visible in the type.

Lemma 2.1 of the manuscript (`DoubleSkewBound`) is **derived**, not assumed —
`RankR/FGP.lean` proves it from `FGPBound` without singular values, the
best-rank-2 approximation identity, or Ky Fan, and `RankR/Extend.lean` reduces
the general `U, V` case to the square one by zero-extension.

**What this does and does not certify.** Lean checks the *deduction* — that the
conclusion follows from the hypothesis, given the formal definitions in
`RankR/Conventions.lean`. It cannot check that those formal definitions
faithfully render the manuscript's informal ones. That correspondence is a
human judgement, which is why `Conventions.lean` states each convention
explicitly (inner products conjugate-linear in the first argument;
$\mathrm{Tr}_U$ = trace *over* $U$; $\mathrm{vec}(|x\rangle\langle y|) = x \otimes \bar y$;
$\mathfrak{so}$ defined by $L^T = -L$, not $L^H = -L$) rather than leaving them
implicit. One rendering is worth singling out:
`FGPBound` quantifies over the explicit two-term form
`M = |u₁⟩⟨v₁| + |u₂⟩⟨v₂|`, which is "Schmidt rank ≤ 2 across the row:col cut"
unrolled rather than a theorem about it.

The sharpness claims around Theorem 1.1 are covered too.
`rank_r_partial_trace_of_FGP_square_exact` is the exact-rank form (`r = rank C`),
`rank_r_partial_trace_of_FGP_square_strict` says the bound is *strict* for
nonzero `C` with `rank C < r`, and `rank_eq_of_eq_rank_r_partial_trace_of_FGP_square`
is the stated consequence: equality for nonzero `C` forces `rank C = r`.

`RankR/OneSided.lean` adds the one-sided bound `‖Tr_j C‖₂² ≤ r‖C‖₂²`
(`lem:one-sided-partial-trace`), also unconditional. The manuscript proved it by
trace-norm duality; here a partial trace of a rank-one operator is a matrix
product, so Hilbert–Schmidt submultiplicativity and Cauchy–Schwarz over the range
factorization suffice, and the Schatten-1 norm appears nowhere.

`RankR/Optimal.lean` closes the other half, and needs no hypothesis at all —
not even Fu–Gao–Park. It builds the extremizer `projWit = P_r ⊗ |v⟩⟨w|`,
computes its rank (`rank_projWit`, exactly `r`) and its four quantities
(`‖C‖₂² = r`, `|Tr C|² = r²|⟨w,v⟩|²`, `‖Tr_U C‖₂² = r²`, `‖Tr_V C‖₂² = r|⟨w,v⟩|²`),
shows it attains equality (`projWit_bound_eq`), and derives the two optimality
statements: any bound `‖Tr_U C‖₂² + ‖Tr_V C‖₂² ≤ a‖C‖₂² + b|Tr C|²` valid at
rank `r` has `a ≥ r` (`le_coeff_hsNormSq_of_bound`), and once `a = r` is fixed,
`b ≥ 1/r` (`inv_le_coeff_trace_of_bound`).

**Not proved here:** Fu–Gao–Park's estimate itself. Nothing else.

Two labelled equations of the manuscript, `eq:Phi-Pminus-TTstar` and
`eq:sos-complete-graph`, are **bypassed rather than proved**: the Bessel-duality
route in `Bessel.lean` never forms the synthesis map as a matrix, which removes
the need for both. They remain unverified as claims about the paper.

## Building

Requires [`elan`](https://github.com/leanprover/elan). Mathlib is the only
dependency.

```bash
lake exe cache get     # Mathlib oleans — do not skip, a source build takes hours
lake build RankR
```

The repository root is the Lake package; `lean-toolchain` pins
`leanprover/lean4:v4.32.0` and `lake-manifest.json` pins the exact Mathlib
revision.

## Layout

| Path | Contents |
| --- | --- |
| `RankR/` | the formalization (24 files) |
| `paper/` | the manuscript |

### The formalization, bottom-up

| File | Contents |
| --- | --- |
| `Conventions` | §1 conventions, `doubleSkew`, the double-skew interface |
| `HS` | Hilbert–Schmidt layer, transported from `EuclideanSpace` |
| `Elementary` | rank monotonicity, the contraction identities, trace–rank bound |
| `Operator` | `qform`, factor placements, marginals |
| `Factor` | range factorization `C = ∑ᵢ|eᵢ⟩⟨dᵢ|` |
| `Main` | `qform` algebra, `HopScaled`, Theorem 1.1 given Proposition 2.2 |
| `Skew` | `skewUnit`, `Kᵀ = K` on `doubleSkew` |
| `Kraus` | `qform (A Y Aᴴ) x = qform Y (Aᴴx)`, PSD preservation |
| `Sectors` | doubled sectors, `Ppos − Pneg = 2·ρ₀ᵀ` |
| `Phi` | the `Φ₄` kernel, `eq:Phi-expansion`, `eq:Phi-rhoT` |
| `Synth` | the synthesis map, `eq:T-by-vertices`, the vertex bound |
| `Frame` | adjoint move, `eq:T-orthogonal` |
| `Edge` | the edgewise double-skew bound — the sole consumer of `hFGP` |
| `Assemble`, `Bessel`, `Restrict`, `Synthesis` | the Bessel-duality chain |
| `Theorem` | Proposition 2.2 and Theorem 1.1 given the double-skew bound |
| `Antisym`, `FGP`, `Extend` | the antisymmetrizer, **Theorem 1.1 from Fu–Gao–Park** |
| `Optimal` | the extremizer, and optimality of the coefficients `r`, `1/r` |
| `OneSided` | HS submultiplicativity, and `lem:one-sided-partial-trace` |
| `Axioms` | the axiom surface, checked by the build |

## A note on provenance

`paper/rank-r.tex` states that its arguments were generated by GPT-5.6, that the
author did not independently derive them, and that no expert has reviewed them.
Fu–Gao–Park was posted three days before the manuscript and is itself
unreviewed. This formalization is therefore a *measuring instrument*, not a
victory lap.
