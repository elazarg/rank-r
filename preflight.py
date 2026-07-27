#!/usr/bin/env python3
"""
Pre-flight numerical checks for paper/rank-r.tex (PLAN.md section 5).

Every check tests a specific labelled equation or inequality of the manuscript
at small dimensions, before any Lean effort is spent on it.  A failure here is
an afternoon; the same failure found at Milestone M3 is everything spent
getting to M3.

Conventions, taken from paper/rank-r.tex section 1:
  - inner products conjugate-linear in the FIRST argument
  - vec(|x><y|) = x (x) conj(y)
  - Tr_U means the partial trace OVER the factor U
  - ||.||_2 is Hilbert-Schmidt
Tensor factors are ordered as written, with index of (a,b,c) equal to
((a*dB)+b)*dC+c, i.e. numpy's kron(kron(A,B),C).
"""

import itertools
import numpy as np

rng = np.random.default_rng(20260727)
TOL = 1e-9

# ---------------------------------------------------------------- utilities


def rand_c(*shape):
    return rng.normal(size=shape) + 1j * rng.normal(size=shape)


def dagger(M):
    return M.conj().T


def hs(A, B):
    """<A,B> = Tr(A^H B), conjugate-linear in the first argument."""
    return np.trace(dagger(A) @ B)


def nsq(A):
    """||A||_2^2."""
    return float(np.real(np.sum(np.abs(A) ** 2)))


def as_tensor(M, dims):
    return M.reshape(list(dims) + list(dims))


def from_tensor(T, dims):
    n = int(np.prod(dims))
    return T.reshape(n, n)


def _ptrace_slow(M, dims, keep):
    n = len(dims)
    T = as_tensor(M, dims)
    cur = list(range(n))  # labels still present
    while len(cur) > len(keep):
        k = next(i for i in cur if i not in keep)
        pos = cur.index(k)
        T = np.trace(T, axis1=pos, axis2=pos + len(cur))
        cur.remove(k)
    # reorder to the requested order
    perm = [cur.index(k) for k in keep]
    m = len(cur)
    T = np.transpose(T, perm + [p + m for p in perm])
    return from_tensor(T, [dims[k] for k in keep])


def ptranspose(M, dims, tfac):
    """Partial transpose on the factors listed in tfac."""
    n = len(dims)
    T = as_tensor(M, dims).copy()
    ax_row = list(range(n))
    ax_col = list(range(n, 2 * n))
    for k in tfac:
        ax_row[k], ax_col[k] = ax_col[k], ax_row[k]
    T = np.transpose(T, ax_row + ax_col)
    return from_tensor(T, dims)


def place(M, sub, dims):
    """Place operator M, which acts on the factors `sub` (in that order),
    onto the full space with dims `dims`, tensoring identity elsewhere.

    This is the manuscript's 'operators are placed on their labeled tensor
    factors, regardless of whether those factors are adjacent'."""
    n = len(dims)
    rest = [i for i in range(n) if i not in sub]
    rest_dim = int(np.prod([dims[i] for i in rest])) if rest else 1
    full = np.kron(M, np.eye(rest_dim))
    order = list(sub) + rest
    T = as_tensor(full, [dims[i] for i in order])
    inv = [order.index(i) for i in range(n)]
    T = np.transpose(T, inv + [p + n for p in inv])
    return from_tensor(T, dims)


def so_basis(d):
    """Standard skew Kraus operators L_ab = E_ab - E_ba, a<b.
    Normalized so that <L,L>_HS = 2 (rank-r.tex, before eq:T-definition)."""
    out = []
    for a in range(d):
        for b in range(a + 1, d):
            L = np.zeros((d, d), dtype=complex)
            L[a, b] = 1.0
            L[b, a] = -1.0
            out.append(L)
    return out


def Lambda(X):
    """Lambda_E(X) = Tr(X) I - X^T."""
    return np.trace(X) * np.eye(X.shape[0]) - X.T


def rand_isometry_cols(n, r):
    """r orthonormal columns in C^n."""
    A = rand_c(n, r)
    Q, _ = np.linalg.qr(A)
    return Q[:, :r]


RESULTS = []


def report(name, ok, detail=""):
    RESULTS.append((name, ok))
    print(f"[{'PASS' if ok else 'FAIL'}] {name}" + (f"  {detail}" if detail else ""))


# ------------------------------------------------- check 0: main inequality


def check_main_inequality():
    """Theorem 1.1, eq:main-bound-exact-rank / eq:main-bound."""
    worst = np.inf
    for (dU, dV) in [(2, 2), (3, 2), (2, 3), (3, 3), (4, 3)]:
        n = dU * dV
        for r in range(1, n + 1):
            for _ in range(200):
                C = rand_c(n, r) @ rand_c(r, n)
                trU = _ptrace_slow(C, (dU, dV), [1])   # trace OVER U
                trV = _ptrace_slow(C, (dU, dV), [0])   # trace OVER V
                lhs = nsq(trU) + nsq(trV)
                rhs = r * nsq(C) + abs(np.trace(C)) ** 2 / r
                worst = min(worst, (rhs - lhs) / max(nsq(C), 1e-300))
    report("Thm 1.1  ||Tr_U C||^2+||Tr_V C||^2 <= r||C||^2+|Tr C|^2/r",
           worst > -TOL, f"min normalized slack = {worst:.3e}")


def check_sharpness():
    """Section 1: C = P_r (x) |v><w| attains equality."""
    bad = []
    for dU, dV, r in [(4, 3, 2), (5, 2, 3), (3, 3, 3)]:
        P = np.zeros((dU, dU), dtype=complex)
        for i in range(r):
            P[i, i] = 1.0
        for orth in (True, False):
            v = np.zeros(dV, dtype=complex); v[0] = 1
            w = np.zeros(dV, dtype=complex)
            w[1 if orth else 0] = 1
            C = np.kron(P, np.outer(v, w.conj()))
            trU = _ptrace_slow(C, (dU, dV), [1])
            trV = _ptrace_slow(C, (dU, dV), [0])
            lhs = nsq(trU) + nsq(trV)
            rhs = r * nsq(C) + abs(np.trace(C)) ** 2 / r
            # paper claims ||Tr_U C||^2=r^2, ||Tr_V C||^2=r|<w,v>|^2,
            #              ||C||^2=r, |Tr C|^2=r^2|<w,v>|^2
            ip = abs(np.vdot(w, v)) ** 2
            claims = [
                (nsq(trU), r ** 2),
                (nsq(trV), r * ip),
                (nsq(C), r),
                (abs(np.trace(C)) ** 2, r ** 2 * ip),
                (lhs, rhs),
            ]
            for got, want in claims:
                if abs(got - want) > 1e-9:
                    bad.append((dU, dV, r, orth, got, want))
    report("Sec 1 sharpness  C = P_r (x) |v><w| gives equality", not bad,
           str(bad[:2]) if bad else "all 4 quantities + equality match")


# ------------------------------- check 1 (D3): Lemma 2.1, the FGP consequence


def check_double_skew(dmax=4, trials=4000):
    """Lemma 2.1 (lem:double-skew): for K in so(U) (x) so(V),
       s_1(K)^2 + s_2(K)^2 <= (1/2) ||K||_2^2.

    This is the consequence the rest of the paper actually consumes, so
    testing it directly is a stronger check than matching index conventions
    against Fu-Gao-Park by hand (PLAN.md, tier D3)."""
    rows = []
    ok = True
    for dU in range(2, dmax + 1):
        for dV in range(2, dmax + 1):
            Ls, Ms = so_basis(dU), so_basis(dV)
            best = -np.inf
            for _ in range(trials):
                c = rand_c(len(Ls), len(Ms))
                K = sum(c[a, b] * np.kron(Ls[a], Ms[b])
                        for a in range(len(Ls)) for b in range(len(Ms)))
                s = np.linalg.svd(K, compute_uv=False)
                ratio = (s[0] ** 2 + s[1] ** 2) / nsq(K)
                best = max(best, ratio)
            rows.append((dU, dV, best))
            if best > 0.5 + 1e-9:
                ok = False
    report("Lem 2.1  s1^2+s2^2 <= (1/2)||K||^2 on so(U)(x)so(V)", ok,
           "max ratio per (dU,dV): " +
           ", ".join(f"{a}x{b}:{v:.6f}" for a, b, v in rows))
    return ok


def check_double_skew_symmetric():
    """Section 2: every K in so(U) (x) so(V) satisfies K^T = K.
    This is what makes eq:T-orthogonal work."""
    bad = 0
    for dU, dV in [(2, 3), (3, 3), (4, 2)]:
        Ls, Ms = so_basis(dU), so_basis(dV)
        for _ in range(50):
            c = rand_c(len(Ls), len(Ms))
            K = sum(c[a, b] * np.kron(Ls[a], Ms[b])
                    for a in range(len(Ls)) for b in range(len(Ms)))
            if np.max(np.abs(K.T - K)) > 1e-10:
                bad += 1
    report("Sec 2  K^T = K for K in so(U)(x)so(V)", bad == 0)


# ------------------------------------- check 2: Lambda_E Kraus form + Phi


def check_lambda_kraus():
    """eq:Lambda-kraus: Lambda_E(X) = sum_{a<b} L_ab X L_ab^*."""
    bad = 0
    for d in (2, 3, 4):
        Ls = so_basis(d)
        for _ in range(50):
            X = rand_c(d, d)
            got = sum(L @ X @ dagger(L) for L in Ls)
            if np.max(np.abs(got - Lambda(X))) > 1e-10:
                bad += 1
    report("eq:Lambda-kraus  Lambda_E(X)=sum_{a<b} L_ab X L_ab^*", bad == 0)


def check_lambda_choi():
    """Section 2: Choi operator of Lambda_E is I - F, spectrum in {0,2}."""
    bad = []
    for d in (2, 3, 4):
        J = np.zeros((d * d, d * d), dtype=complex)
        for i in range(d):
            for j in range(d):
                E = np.zeros((d, d), dtype=complex)
                E[i, j] = 1
                J += np.kron(np.outer(np.eye(d)[i], np.eye(d)[j]), Lambda(E))
        F = np.zeros((d * d, d * d), dtype=complex)
        for i in range(d):
            for j in range(d):
                F[i * d + j, j * d + i] = 1
        if np.max(np.abs(J - (np.eye(d * d) - F))) > 1e-10:
            bad.append(("J != I-F", d))
        ev = np.linalg.eigvalsh(J)
        if np.min(ev) < -1e-10 or np.max(np.abs(ev * (ev - 2))) > 1e-9:
            bad.append(("spec", d, ev))
    report("Sec 2  Choi(Lambda_E) = I - F, spectrum in {0,2}", not bad, str(bad[:1]))


def check_phi_expansion():
    """eq:Phi-expansion, the four-term expansion of Phi = Lambda_U (x) Lambda_V (x) id_Q.
    PLAN.md tier D2, item 2 -- the transpose/placement bookkeeping."""
    bad = []
    for dU, dV, dQ in [(2, 2, 2), (3, 2, 2), (2, 3, 3)]:
        dims = (dU, dV, dQ)
        Ls, Ms = so_basis(dU), so_basis(dV)
        kraus = [np.kron(np.kron(L, M), np.eye(dQ)) for L in Ls for M in Ms]
        for _ in range(30):
            Y = rand_c(dU * dV * dQ, dU * dV * dQ)
            via_kraus = sum(K @ Y @ dagger(K) for K in kraus)

            t1 = place(_ptrace_slow(Y, dims, [2]), [2], dims)          # I_UV (x) Tr_UV Y
            trU = _ptrace_slow(Y, dims, [1, 2])                        # on V,Q
            t2 = place(ptranspose(trU, (dV, dQ), [0]), [1, 2], dims)   # I_U (x) (Tr_U Y)^{T_V}
            trV = _ptrace_slow(Y, dims, [0, 2])                        # on U,Q
            t3 = place(ptranspose(trV, (dU, dQ), [0]), [0, 2], dims)   # (Tr_V Y)^{T_U} (x) I_V
            t4 = ptranspose(Y, dims, [0, 1])                           # Y^{T_UV}
            via_formula = t1 - t2 - t3 + t4

            if np.max(np.abs(via_kraus - via_formula)) > 1e-8:
                bad.append((dU, dV, dQ,
                            float(np.max(np.abs(via_kraus - via_formula)))))
                break
    report("eq:Phi-expansion  Phi(Y) = I(x)Tr_UV Y - I_U(x)(Tr_U Y)^{T_V} "
           "- (Tr_V Y)^{T_U}(x)I_V + Y^{T_UV}", not bad, str(bad[:1]))


# --------------------------------- check 3: the H_r machinery (Prop 2.2)


def build_code(dU, dV, r):
    """psi, rho, P_pm, and the orthonormal family {e_i} of Prop 2.2."""
    n = dU * dV
    E = rand_isometry_cols(n, r)               # columns e_i
    e = [E[:, i] for i in range(r)]
    q = [np.eye(r)[:, i] for i in range(r)]
    psi = sum(np.kron(e[i], q[i]) for i in range(r)) / np.sqrt(r)
    rho = np.outer(psi, psi.conj())
    return e, q, psi, rho


def check_rho_partial_transpose():
    """eq:rho-partial-transpose-expanded and eq:rho-partial-transpose."""
    bad = []
    for dU, dV, r in [(2, 2, 2), (2, 2, 3), (3, 2, 3), (3, 3, 4)]:
        n = dU * dV
        e, q, psi, rho = build_code(dU, dV, r)
        rhoT = ptranspose(rho, (n, r), [0])

        expanded = sum(
            np.outer(np.kron(e[j].conj(), q[i]), np.kron(e[i].conj(), q[j]).conj())
            for i in range(r) for j in range(r)) / r
        if np.max(np.abs(rhoT - expanded)) > 1e-9:
            bad.append(("expanded", dU, dV, r))

        eta = {}
        for i in range(r):
            for j in range(i + 1, r):
                eta[(i, j)] = (np.kron(e[i].conj(), q[j])
                               - np.kron(e[j].conj(), q[i])) / np.sqrt(2)
        Pm = sum(np.outer(v, v.conj()) for v in eta.values())
        # P_+ = projection onto the symmetric part of S (x) Q
        sym = []
        for i in range(r):
            sym.append(np.kron(e[i].conj(), q[i]))
        for i in range(r):
            for j in range(i + 1, r):
                sym.append((np.kron(e[i].conj(), q[j])
                            + np.kron(e[j].conj(), q[i])) / np.sqrt(2))
        Pp = sum(np.outer(v, v.conj()) for v in sym)
        if np.max(np.abs(rhoT - (Pp - Pm) / r)) > 1e-9:
            bad.append(("Ppm", dU, dV, r))
    report("eq:rho-partial-transpose  rho^{T_UV} = (1/r)(P_+ - P_-)", not bad,
           str(bad[:2]))


def check_T_machinery():
    """eq:T-definition, eq:T-by-vertices, eq:T-Cauchy, eq:T-operator-bound,
    eq:T-orthogonal, eq:Phi-Pminus-TTstar.
    PLAN.md tier D2, item 1 -- the constant chain that must land on exactly (r-1)."""
    bad = []
    worst_ratio = -np.inf
    worst_orth = 0.0
    for dU, dV, r in [(2, 2, 2), (2, 2, 3), (3, 2, 3), (3, 3, 4), (3, 3, 2), (4, 2, 4)]:
        n = dU * dV
        Ls, Ms = so_basis(dU), so_basis(dV)
        nL, nM = len(Ls), len(Ms)
        e, q, psi, rho = build_code(dU, dV, r)
        eta = {}
        for i in range(r):
            for j in range(i + 1, r):
                eta[(i, j)] = (np.kron(e[i].conj(), q[j])
                               - np.kron(e[j].conj(), q[i])) / np.sqrt(2)
        edges = sorted(eta.keys())

        def Tc(c):
            out = np.zeros(n * r, dtype=complex)
            for (i, j) in edges:
                for a in range(nL):
                    for b in range(nM):
                        op = np.kron(np.kron(Ls[a], Ms[b]), np.eye(r))
                        out = out + c[(i, j)][a, b] * (op @ eta[(i, j)])
            return out

        for _ in range(60):
            c = {ed: rand_c(nL, nM) for ed in edges}
            cn = sum(nsq(c[ed]) for ed in edges)
            t = Tc(c)
            # normalized by the claimed bound (r-1): must stay <= 1
            ratio = nsq(t.reshape(-1, 1)) / (cn * (r - 1))
            worst_ratio = max(worst_ratio, ratio)

            # eq:T-by-vertices
            K = {ed: sum(c[ed][a, b] * np.kron(Ls[a], Ms[b])
                         for a in range(nL) for b in range(nM)) for ed in edges}
            byvert = np.zeros(n * r, dtype=complex)
            for k in range(r):
                acc = np.zeros(n, dtype=complex)
                for i in range(k):
                    acc = acc + K[(i, k)] @ e[i].conj()
                for j in range(k + 1, r):
                    acc = acc - K[(k, j)] @ e[j].conj()
                byvert = byvert + np.kron(acc, q[k])
            byvert = byvert / np.sqrt(2)
            if np.max(np.abs(byvert - t)) > 1e-8:
                bad.append(("eq:T-by-vertices", dU, dV, r))
                break

            # eq:Kc-norm : ||K^{(ij)}||^2 = 4||c^{(ij)}||^2
            off = [ed for ed in edges if abs(nsq(K[ed]) - 4 * nsq(c[ed])) > 1e-8]
            if off:
                ed = off[0]
                bad.append(("eq:Kc-norm", dU, dV, r, nsq(K[ed]), 4 * nsq(c[ed])))
                break

            # eq:T-orthogonal : <psi, Tc> = 0
            worst_orth = max(worst_orth, abs(np.vdot(psi, t)))

        # eq:Phi-Pminus-TTstar : Phi(P_-) = T T^*
        Pm = sum(np.outer(v, v.conj()) for v in eta.values())
        kraus = [np.kron(np.kron(L, M), np.eye(r)) for L in Ls for M in Ms]
        PhiPm = sum(Kk @ Pm @ dagger(Kk) for Kk in kraus)
        cols = []
        for (i, j) in edges:
            for a in range(nL):
                for b in range(nM):
                    op = np.kron(np.kron(Ls[a], Ms[b]), np.eye(r))
                    cols.append(op @ eta[(i, j)])
        T = np.array(cols).T
        if np.max(np.abs(PhiPm - T @ dagger(T))) > 1e-8:
            bad.append(("eq:Phi-Pminus-TTstar", dU, dV, r))
        # eq:T-operator-bound as an operator norm statement
        if np.linalg.norm(T, 2) ** 2 > (r - 1) + 1e-7:
            bad.append(("||T||^2 <= r-1", dU, dV, r, np.linalg.norm(T, 2) ** 2))

    report("eq:T-operator-bound  ||Tc||^2 <= (r-1)||c||^2  (the constant chain)",
           worst_ratio <= 1.0 + 1e-7,
           f"max ||Tc||^2/((r-1)||c||^2) over trials = {worst_ratio:.6f}")
    report("eq:T-orthogonal  <psi, Tc> = 0", worst_orth < 1e-9,
           f"max |<psi,Tc>| = {worst_orth:.3e}")
    report("eq:Phi-Pminus-TTstar / eq:Kc-norm / eq:T-by-vertices", not bad,
           str(bad[:2]))


def check_Hr_psd():
    """Proposition 2.2 (prop:operator_ineq): H_r >= 0.  The load-bearing claim."""
    worst = np.inf
    bad = []
    # r = 1 is degenerate -- the complete graph K_1 has no edges, so the
    # T-bound is vacuous and H reduces to Phi(P_+) -- but the Lean assembly
    # consumes it for every rank-one C, so it must be covered.
    for dU, dV, r in [(2, 2, 1), (3, 2, 1), (2, 3, 1), (3, 3, 1), (4, 3, 1),
                      (2, 2, 2), (2, 2, 3), (2, 2, 4), (3, 2, 3), (3, 2, 5),
                      (3, 3, 4), (3, 3, 2), (4, 2, 4), (4, 3, 6)]:
        n = dU * dV
        dims = (dU, dV, r)
        for _ in range(60):
            e, q, psi, rho = build_code(dU, dV, r)
            rho_UQ = _ptrace_slow(rho, dims, [0, 2])   # trace out V
            rho_VQ = _ptrace_slow(rho, dims, [1, 2])   # trace out U
            H = (np.eye(n * r) + rho / r
                 - place(rho_UQ, [0, 2], dims)
                 - place(rho_VQ, [1, 2], dims))
            ev = np.linalg.eigvalsh((H + dagger(H)) / 2)
            worst = min(worst, float(ev[0]))
            if ev[0] < -1e-8:
                bad.append((dU, dV, r, ev[0]))
    report("Prop 2.2  H_r = I + rho/r - rho_UQ(x)I_V - I_U(x)rho_VQ >= 0",
           not bad, f"min eigenvalue over all trials = {worst:.3e}")


def check_H_decomposition():
    """eq:H-decomposition: H_r = (1/r)Phi(P_+) + (1/r)[(r-1)(I-rho) - Phi(P_-)]."""
    bad = []
    for dU, dV, r in [(2, 2, 2), (3, 2, 3), (3, 3, 4)]:
        n = dU * dV
        dims = (dU, dV, r)
        Ls, Ms = so_basis(dU), so_basis(dV)
        kraus = [np.kron(np.kron(L, M), np.eye(r)) for L in Ls for M in Ms]
        for _ in range(20):
            e, q, psi, rho = build_code(dU, dV, r)
            rho_UQ = _ptrace_slow(rho, dims, [0, 2])
            rho_VQ = _ptrace_slow(rho, dims, [1, 2])
            H = (np.eye(n * r) + rho / r
                 - place(rho_UQ, [0, 2], dims)
                 - place(rho_VQ, [1, 2], dims))
            eta = {}
            for i in range(r):
                for j in range(i + 1, r):
                    eta[(i, j)] = (np.kron(e[i].conj(), q[j])
                                   - np.kron(e[j].conj(), q[i])) / np.sqrt(2)
            Pm = sum(np.outer(v, v.conj()) for v in eta.values())
            rhoT = ptranspose(rho, (n, r), [0])
            Pp = r * rhoT + Pm
            PhiPp = sum(K @ Pp @ dagger(K) for K in kraus)
            PhiPm = sum(K @ Pm @ dagger(K) for K in kraus)
            rhs = PhiPp / r + ((r - 1) * (np.eye(n * r) - rho) - PhiPm) / r
            if np.max(np.abs(H - rhs)) > 1e-8:
                bad.append((dU, dV, r, float(np.max(np.abs(H - rhs)))))
                break
    report("eq:H-decomposition", not bad, str(bad[:1]))


def check_complete_graph_identity():
    """eq:sos-complete-graph (Prop 4.3) -- claimed as an EXACT identity,
    not an inequality.  PLAN.md tier D2, item 4."""
    bad = []
    worst = 0.0
    for dU, dV, r in [(2, 2, 3), (3, 2, 3), (3, 3, 4), (3, 2, 5), (2, 2, 2)]:
        n = dU * dV
        Ls, Ms = so_basis(dU), so_basis(dV)
        nL, nM = len(Ls), len(Ms)
        e, q, psi, rho = build_code(dU, dV, r)
        eta = {}
        for i in range(r):
            for j in range(i + 1, r):
                eta[(i, j)] = (np.kron(e[i].conj(), q[j])
                               - np.kron(e[j].conj(), q[i])) / np.sqrt(2)
        edges = sorted(eta.keys())
        for _ in range(40):
            c = {ed: rand_c(nL, nM) for ed in edges}
            K = {ed: sum(c[ed][a, b] * np.kron(Ls[a], Ms[b])
                         for a in range(nL) for b in range(nM)) for ed in edges}
            t = np.zeros(n * r, dtype=complex)
            for k in range(r):
                acc = np.zeros(n, dtype=complex)
                for i in range(k):
                    acc = acc + K[(i, k)] @ e[i].conj()
                for j in range(k + 1, r):
                    acc = acc - K[(k, j)] @ e[j].conj()
                t = t + np.kron(acc, q[k])
            t = t / np.sqrt(2)
            lhs = (r - 1) * sum(nsq(c[ed]) for ed in edges) - nsq(t.reshape(-1, 1))

            edge_terms = 0.0
            for (i, j) in edges:
                edge_terms += (0.5 * nsq(K[(i, j)])
                               - nsq((K[(i, j)] @ e[i].conj()).reshape(-1, 1))
                               - nsq((K[(i, j)] @ e[j].conj()).reshape(-1, 1)))
            vertex_terms = 0.0
            for k in range(r):
                vs = []
                for i in range(k):
                    vs.append(K[(i, k)] @ e[i].conj())
                for j in range(k + 1, r):
                    vs.append(-(K[(k, j)] @ e[j].conj()))
                for x in range(len(vs)):
                    for y in range(x + 1, len(vs)):
                        vertex_terms += nsq((vs[x] - vs[y]).reshape(-1, 1))
            rhs = (r - 1) / 2 * edge_terms + 0.5 * vertex_terms
            worst = max(worst, abs(lhs - rhs) / max(abs(lhs), 1.0))
            if abs(lhs - rhs) > 1e-7 * max(abs(lhs), 1.0):
                bad.append((dU, dV, r, lhs, rhs))
                break
    report("eq:sos-complete-graph  (exact identity, not a bound)", not bad,
           f"max relative discrepancy = {worst:.3e}" if not bad else str(bad[:1]))


# --------------------------------------------- check 4: sections 5 and 8


def check_prop22_bracket():
    """The exact residual of Proposition 2.2 after the sector decomposition.

    With rho0 = |delta_e><delta_e| (unnormalized), Ppos = 2P_+, Pneg = 2P_- and
    Phi = Lambda_U (x) Lambda_V (x) id, the scaled decomposition reads

        2 s^2 H = s Phi(Ppos) + [ 2s(s-1) I - 2(s-1) rho0 - s Phi(Pneg) ].

    Phi(Ppos) is PSD because Ppos is and Phi is a Kraus sum, so ALL remaining
    content of Prop 2.2 is that the bracket is PSD.  This isolates exactly what
    the complete-graph argument has to deliver.

    The bracket is SINGULAR in every case tested, but that is structural rather
    than a sign of tightness: delta_e lies in its kernel by construction, since
    every column of the synthesis map is orthogonal to delta_e (eq:T-orthogonal)
    and rho0 delta_e = s delta_e.  On delta_e's orthogonal complement the
    bracket's positivity is equivalent to the frame bound ||W||^2 <= 2(s-1),
    which is attained at (dU,dV,s) = (2,2,2) but has slack elsewhere.
    """
    bad = []
    rows = []
    for dU, dV, s in [(2, 2, 1), (2, 2, 2), (3, 2, 3), (2, 3, 2), (3, 3, 4),
                      (4, 2, 2), (3, 3, 2)]:
        n = dU * dV
        N = n * s
        dims = (dU, dV, s)
        for _ in range(10):
            e, q, psi, rho = build_code(dU, dV, s)
            rho0 = s * rho
            T = ptranspose(rho0, (n, s), [0])
            Ls, Ms = so_basis(dU), so_basis(dV)
            kraus = [np.kron(np.kron(L, M), np.eye(s)) for L in Ls for M in Ms]
            Phi = lambda Y: sum(K @ Y @ dagger(K) for K in kraus)
            ebar = [np.conj(v) for v in e]
            eps = {}
            for j in range(s):
                for k in range(s):
                    eps[(j, k)] = np.kron(ebar[j], np.eye(s)[:, k])
            ro = lambda x, y: np.outer(x, y.conj())
            Ppos = 2 * sum(ro(eps[(i, i)], eps[(i, i)]) for i in range(s))
            Pneg = np.zeros((N, N), dtype=complex)
            for i in range(s):
                for j in range(i + 1, s):
                    sg = eps[(i, j)] + eps[(j, i)]
                    zt = eps[(i, j)] - eps[(j, i)]
                    Ppos = Ppos + ro(sg, sg)
                    Pneg = Pneg + ro(zt, zt)
            if np.max(np.abs((Ppos - Pneg) - 2 * T)) > 1e-8:
                bad.append(("sector identity", dU, dV, s))
            rho_UQ = _ptrace_slow(rho, dims, [0, 2])
            rho_VQ = _ptrace_slow(rho, dims, [1, 2])
            H = (np.eye(N) + rho / s
                 - place(rho_UQ, [0, 2], dims) - place(rho_VQ, [1, 2], dims))
            brack = (2 * s * (s - 1) * np.eye(N) - 2 * (s - 1) * rho0
                     - s * Phi(Pneg))
            if np.max(np.abs(2 * s * s * H - (s * Phi(Ppos) + brack))) > 1e-7:
                bad.append(("decomposition", dU, dV, s))
            ev = np.linalg.eigvalsh((brack + dagger(brack)) / 2)
            rows.append(float(ev[0]))
            if ev[0] < -1e-7:
                bad.append(("bracket not PSD", dU, dV, s, float(ev[0])))
    report("Prop 2.2 residual  2s^2.H = s.Phi(Ppos) + bracket, bracket >= 0",
           not bad,
           f"min eigenvalue of bracket over all trials = {min(rows):.3e} "
           f"(kernel contains delta_e by construction)"
           if not bad else str(bad[:3]))


def check_q2_score_curve():
    """prop:exact-q2-score: mu_r(t) = (1-t)(1-rt) for t<=1/r, 1-rt for t>=1/r."""
    bad = []
    for d in (2, 3, 4):
        for r in range(1, d + 1):
            for t in [0.0, 0.1, 0.3, 1.0 / r * 0.5, 1.0 / r, 1.0 / r * 1.5, 1.0, 2.0]:
                pred = (1 - t) * (1 - r * t) if t <= 1 / r else 1 - r * t
                best = np.inf
                for _ in range(3000):
                    C = rand_c(d * d, r) @ rand_c(r, d * d)
                    tr1 = _ptrace_slow(C, (d, d), [1])
                    tr2 = _ptrace_slow(C, (d, d), [0])
                    q = (nsq(C) - t * (nsq(tr1) + nsq(tr2))
                         + t ** 2 * abs(np.trace(C)) ** 2)
                    best = min(best, q / nsq(C))
                # extremizers from the paper
                P = np.zeros((d, d), dtype=complex)
                for i in range(r):
                    P[i, i] = 1
                for orth in (True, False):
                    v = np.zeros(d, dtype=complex); v[0] = 1
                    w = np.zeros(d, dtype=complex); w[1 if orth else 0] = 1
                    C = np.kron(P, np.outer(v, w.conj()))
                    tr1 = _ptrace_slow(C, (d, d), [1])
                    tr2 = _ptrace_slow(C, (d, d), [0])
                    q = (nsq(C) - t * (nsq(tr1) + nsq(tr2))
                         + t ** 2 * abs(np.trace(C)) ** 2)
                    best = min(best, q / nsq(C))
                if best < pred - 1e-7:
                    bad.append(("below", d, r, t, best, pred))
                elif best > pred + 1e-6:
                    bad.append(("not attained", d, r, t, best, pred))
    report("prop:exact-q2-score  mu_r(t) formula", not bad, str(bad[:3]))


def check_asymmetric_score():
    """thm:exact-asymmetric-score, eq:exact-asymmetric-score.

    This is the ONLY place where getting `Tr_U` = 'trace over U' backwards is
    visible: Theorem 1.1 is symmetric in U and V, so a swapped convention
    survives it undetected (PLAN.md tier D0).  Here a and b are attached to
    different factors, so a swap breaks the m = max / l = min structure."""
    bad = []
    for d in (2, 3):
        for r in range(1, d + 1):
            for a in [0.0, 0.2, 1.0 / r, 0.6, 1.0, 1.7]:
                for b in [0.0, 0.2, 1.0 / r, 0.6, 1.0, 1.7]:
                    mm, ll = max(a, b), min(a, b)
                    pred = ((1 - ll) * (1 - r * mm) if mm <= 1 / r
                            else 1 - r * mm)
                    best = np.inf
                    cands = []
                    for _ in range(2000):
                        cands.append(rand_c(d * d, r) @ rand_c(r, d * d))
                    # the paper's extremizers, on both factors
                    P = np.zeros((d, d), dtype=complex)
                    for i in range(r):
                        P[i, i] = 1
                    for orth in (True, False):
                        v = np.zeros(d, dtype=complex); v[0] = 1
                        w = np.zeros(d, dtype=complex); w[1 if orth else 0] = 1
                        cands.append(np.kron(P, np.outer(v, w.conj())))
                        cands.append(np.kron(np.outer(v, w.conj()), P))
                    for C in cands:
                        tr1 = _ptrace_slow(C, (d, d), [1])   # over copy 1
                        tr2 = _ptrace_slow(C, (d, d), [0])   # over copy 2
                        q = (nsq(C) - a * nsq(tr1) - b * nsq(tr2)
                             + a * b * abs(np.trace(C)) ** 2)
                        best = min(best, q / nsq(C))
                    if best < pred - 1e-7:
                        bad.append(("below", d, r, a, b, best, pred))
                    elif best > pred + 1e-6:
                        bad.append(("not attained", d, r, a, b, best, pred))
    report("thm:exact-asymmetric-score  (also the Tr_U convention check)",
           not bad, str(bad[:3]))


def check_mfold_regimes():
    """thm:mfold-regimes items (1) and (2): Z_t^{(m)} is 1-block-positive iff
    t <= 1, and r-block-positive for r >= d iff t <= 1/d.  PLAN.md tier D2,
    item 7 -- highest per-item risk, nothing else depends on it."""
    bad = []

    def qm(C, t, d, m):
        perm = []
        for j in range(m):
            perm += [j, m + j]
        Om = np.zeros((d * d,), dtype=complex)
        for i in range(d):
            Om[i * d + i] = 1
        Z = np.array([[1.0]], dtype=complex)
        for _ in range(m):
            Z = np.kron(Z, np.eye(d * d) - t * np.outer(Om, Om.conj()))
        v = np.transpose(C.reshape([d] * m + [d] * m), perm).reshape(-1)
        return float(np.real(np.vdot(v, Z @ v))) / nsq(C)

    for d, m in [(2, 2), (2, 3), (3, 2)]:
        n = d ** m
        v0 = np.zeros(d, dtype=complex); v0[0] = 1
        w0 = np.zeros(d, dtype=complex); w0[1] = 1
        for t in [0.5, 0.9, 1.0, 1.1, 1.6]:
            # (1) r = 1
            worst = np.inf
            for _ in range(2000):
                C = rand_c(n, 1) @ rand_c(1, n)
                worst = min(worst, qm(C, t, d, m))
            # hard-coded extremal rank-1 witness, so this direction does not
            # depend on random sampling finding it
            for j in range(m):
                C = np.array([[1.0]], dtype=complex)
                for k in range(m):
                    C = np.kron(C, np.outer(v0, v0.conj()) if k == j
                                else np.outer(v0, w0.conj()))
                assert np.linalg.matrix_rank(C) == 1
                worst = min(worst, qm(C, t, d, m))
            if (worst >= -1e-7) != (t <= 1 + 1e-9):
                bad.append(("r=1", d, m, t, worst))
        for t in [1 / d * 0.8, 1 / d, 1 / d * 1.2, 0.6, 0.9]:
            # (2) r >= d  (take r = n, i.e. unconstrained rank).
            # Random full-rank Gaussians do NOT find the violator: it is the
            # extremal product I_d (x) |v><w|^{(x)(m-1)} with v _|_ w, which
            # has q_m = d(1-td) by multiplicativity (eq:mfold-multiplicativity).
            worst = np.inf
            for _ in range(2000):
                C = rand_c(n, n)
                worst = min(worst, qm(C, t, d, m))
            v = np.zeros(d, dtype=complex); v[0] = 1
            w = np.zeros(d, dtype=complex); w[1] = 1
            spectator = np.outer(v, w.conj())
            for j in range(m):
                C = np.array([[1.0]], dtype=complex)
                for k in range(m):
                    C = np.kron(C, np.eye(d) if k == j else spectator)
                worst = min(worst, qm(C, t, d, m))
            if (worst >= -1e-7) != (t <= 1 / d + 1e-9):
                bad.append(("r>=d", d, m, t, worst))
    report("thm:mfold-regimes (1) r=1 iff t<=1, (2) r>=d iff t<=1/d",
           not bad, str(bad[:3]))


def check_fgp_index_matching():
    """Tier D3: the index matching between Fu-Gao-Park Thm 2.4 as published and
    the manuscript's application of it in lem:double-skew.

    FGP states its bound for antisymmetric pairs (1,3) and (2,4) of (C^d)^{(x)4}
    with the Schmidt cut 12:34.  The manuscript applies it to pairs
    (U_out, U_in), (V_out, V_in) with the crossed cut
    (U_out V_out) : (U_in V_in).  Under the labeling
    1 = U_out, 2 = V_out, 3 = U_in, 4 = V_in these must be the same operator and
    the same cut; the manuscript asserts this without exhibiting it.

    Four things are checked:
      (a) Q- = Pi_A^{(13)} (x) Pi_A^{(24)} is a projection and the factors commute;
      (b) rank(Q-) equals dim(so(d) (x) so(d)) -- so the range of Q- is exactly
          the vectorized double-skew space, not merely contains it;
      (c) vec(K) is FIXED by Q- for K in so(x)so, with vec entrywise as fixed in
          section 1 -- this is the labeling claim itself;
      (d) FGP's own bound: max <z|Q-|z> over unit z of Schmidt rank <= 2 across
          the 12:34 cut equals 1/2.
    """
    import itertools
    from scipy.optimize import minimize
    rows = []
    bad = []
    for d in (2, 3):
        D = d ** 4

        def swap(p, q):
            S = np.zeros((D, D), dtype=complex)
            for idx in itertools.product(range(d), repeat=4):
                j = list(idx); j[p], j[q] = j[q], j[p]
                S[np.ravel_multi_index(tuple(j), (d,) * 4),
                  np.ravel_multi_index(idx, (d,) * 4)] = 1
            return S

        I = np.eye(D)
        PA13 = (I - swap(0, 2)) / 2
        PA24 = (I - swap(1, 3)) / 2
        Qm = PA13 @ PA24
        if np.max(np.abs(Qm @ Qm - Qm)) > 1e-10:
            bad.append(("not a projection", d))
        if np.max(np.abs(PA13 @ PA24 - PA24 @ PA13)) > 1e-10:
            bad.append(("factors do not commute", d))
        if np.linalg.matrix_rank(Qm, tol=1e-9) != (d * (d - 1) // 2) ** 2:
            bad.append(("rank mismatch", d))
        Ls = so_basis(d)
        for _ in range(20):
            c = rand_c(len(Ls), len(Ls))
            K = sum(c[i, j] * np.kron(Ls[i], Ls[j])
                    for i in range(len(Ls)) for j in range(len(Ls)))
            v = K.reshape(-1)          # (a, b, a', b') = (U_out, V_out, U_in, V_in)
            if np.max(np.abs(Qm @ v - v)) > 1e-9 * max(np.linalg.norm(v), 1.0):
                bad.append(("vec K not fixed by Q-", d))
                break
        nc = 2 * d * d

        def neg(par):
            A = par[:2 * nc].reshape(nc, 2); u = (A[:, 0] + 1j * A[:, 1]).reshape(2, d * d)
            B = par[2 * nc:].reshape(nc, 2); w = (B[:, 0] + 1j * B[:, 1]).reshape(2, d * d)
            z = (np.outer(u[0], w[0]) + np.outer(u[1], w[1])).reshape(-1)
            nz = np.linalg.norm(z)
            if nz < 1e-12:
                return 0.0
            z = z / nz
            return -float(np.real(np.vdot(z, Qm @ z)))

        best = 0.0
        for _ in range(20):
            res = minimize(neg, rng.normal(size=4 * nc), method="L-BFGS-B",
                           options={"maxiter": 3000})
            best = max(best, -res.fun)
        rows.append((d, best))
        if best > 0.5 + 1e-6:
            bad.append(("FGP bound exceeded", d, best))
    report("Tier D3  FGP index matching + Thm 2.4 bound", not bad,
           "max <z|Q-|z> over SR<=2: " + ", ".join(f"d={d}:{v:.6f}" for d, v in rows)
           if not bad else str(bad[:3]))


def check_kronecker_bound():
    """cor:kronecker, eq:kronecker-bound."""
    bad = []
    for d in (2, 3, 4, 5):
        for _ in range(300):
            A = rand_c(d, d); A -= np.trace(A) / d * np.eye(d)
            B = rand_c(d, d); B -= np.trace(B) / d * np.eye(d)
            M = np.kron(A, np.eye(d)) + np.kron(np.eye(d), B)
            s = np.linalg.svd(M, compute_uv=False)
            for k in range(1, d * d + 1):
                lhs = float(np.sum(s[:k] ** 2))
                rhs = min(d, k + max(0.0, 1 - 2 * k / d)) * (nsq(A) + nsq(B))
                if lhs > rhs + 1e-7:
                    bad.append((d, k, lhs, rhs))
    report("cor:kronecker  eq:kronecker-bound", not bad, str(bad[:3]))


def check_mfold_inclusion_exclusion():
    """prop:mfold-inclusion-exclusion, eq:mfold-inclusion-exclusion."""
    bad = []
    for d, m in [(2, 2), (2, 3), (3, 2)]:
        n = d ** m                   # C is an operator on (C^d)^{(x)m}
        Om = np.zeros((d * d,), dtype=complex)
        for i in range(d):
            Om[i * d + i] = 1
        Q1 = np.outer(Om, Om.conj())
        for t in (0.3, 0.7, 1.3):
            Z = np.array([[1.0]], dtype=complex)
            for _ in range(m):
                Z = np.kron(Z, np.eye(d * d) - t * Q1)
            for _ in range(20):
                C = rand_c(n, n)
                # vec is entrywise (sec 1), but Z acts on matched output-input
                # pairs, so reindex (a_1..a_m, b_1..b_m) -> (a_1,b_1,...,a_m,b_m)
                perm = []
                for j in range(m):
                    perm += [j, m + j]
                v = np.transpose(C.reshape([d] * m + [d] * m), perm).reshape(-1)
                lhs = np.real(np.vdot(v, Z @ v))
                rhs = 0.0
                for k in range(m + 1):
                    for S in itertools.combinations(range(m), k):
                        keep = [i for i in range(m) if i not in S]
                        # trace over the copies in S, on the matrix C viewed
                        # as an operator on (C^d)^{(x)m}
                        Cm = C.reshape([d] * m + [d] * m)
                        cur = list(range(m))
                        T = Cm
                        for j in sorted(S, reverse=True):
                            pos = cur.index(j)
                            T = np.trace(T, axis1=pos, axis2=pos + len(cur))
                            cur.remove(j)
                        rhs += (-t) ** k * float(np.sum(np.abs(T) ** 2))
                if abs(lhs - rhs) > 1e-7 * max(abs(rhs), 1.0):
                    bad.append((d, m, t, lhs, rhs))
                    break
    report("prop:mfold-inclusion-exclusion  q_m(t,C)=sum_S (-t)^|S| ||Tr_S C||^2",
           not bad, str(bad[:1]))


# ------------------------------------------------------------------- main

if __name__ == "__main__":
    print("=" * 78)
    print("PRE-FLIGHT CHECKS FOR rank-r.tex")
    print("=" * 78)

    print("\n-- Theorem 1.1 and its sharpness --")
    check_main_inequality()
    check_sharpness()

    print("\n-- Lemma 2.1: the Fu-Gao-Park consequence (tier D3) --")
    check_double_skew()
    check_double_skew_symmetric()
    check_fgp_index_matching()

    print("\n-- The completely positive map Lambda_E --")
    check_lambda_kraus()
    check_lambda_choi()
    check_phi_expansion()

    print("\n-- Proposition 2.2 and the complete-graph machinery (tier D2) --")
    check_rho_partial_transpose()
    check_T_machinery()
    check_Hr_psd()
    check_H_decomposition()
    check_complete_graph_identity()
    check_prop22_bracket()

    print("\n-- Sections 5, 7, 8 --")
    check_q2_score_curve()
    check_asymmetric_score()
    check_mfold_inclusion_exclusion()
    check_mfold_regimes()
    check_kronecker_bound()

    print("\n" + "=" * 78)
    npass = sum(1 for _, ok in RESULTS if ok)
    print(f"{npass}/{len(RESULTS)} checks passed")
    for name, ok in RESULTS:
        if not ok:
            print(f"  FAILED: {name}")
