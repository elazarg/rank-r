/-
Conventions for the formalization of

  E. Gershuni, "A Sharp Rank-r Partial-Trace Inequality via Double-Skew
  Singular-Value Bounds" (rank-r.tex, July 2026)

This file pins down every convention fixed in section 1 of the paper, states the
main theorem, and states the interface to the one imported black box
(Fu-Gao-Park, arXiv:2607.21367, Thm 2.4).

The *statements* are the deliverable of Milestone 0 in PLAN.md: they are where
an LLM-authored manuscript is most likely to be silently inconsistent, and they
cost almost nothing to write down.

Sections are split by which instances are genuinely needed: Lean's `variable`
inclusion heuristic pulls in every instance-implicit whose type mentions an
included variable, so a single omnibus `variable` line silently gives `vec` a
spurious `[DecidableEq m]` argument.
-/
import Mathlib
import QuantumInfo.ForMathlib.Matrix

namespace RankR

open Matrix ComplexConjugate
open scoped Kronecker

/-! ## Section 1 conventions -/

section Generic

variable {m n : Type*} [Fintype m] [Fintype n]

/-- Hilbert-Schmidt inner product `⟪A, B⟫ = Tr(Aᴴ B)`.

PAPER CONVENTION (section 1): "Inner products are conjugate-linear in the first
argument and linear in the second."  This matches Mathlib's `⟪·,·⟫_ℂ`, so no
convention flip is needed anywhere.  Recorded explicitly because a flip here
would silently transpose `Tr C` and `conj (Tr C)` throughout section 3. -/
noncomputable def hsInner (A B : Matrix m n ℂ) : ℂ := (Aᴴ * B).trace

/-- `‖A‖₂²`, the squared Hilbert-Schmidt (Schatten-2, Frobenius) norm.

Defined by hand: Mathlib has `Matrix.frobenius_norm_def` but exposes it only
through the *scoped, non-instance* `Matrix.frobeniusNormedAddCommGroup`, and
has no Frobenius `InnerProductSpace` at all.  Physlib's Frobenius inner-product
section (`QuantumInfo/ForMathlib/Matrix.lean`, ~line 500) is commented out.
See PLAN.md gap A; the bridge to Mathlib's `EuclideanSpace` is in `RankR.HS`. -/
def hsNormSq (A : Matrix m n ℂ) : ℝ := ∑ i, ∑ j, Complex.normSq (A i j)

/-- Vectorization, normalized by `vec (|x⟩⟨y|) = x ⊗ conj y` (section 1).

For matrices this is literally the identity on entries: `|x⟩⟨y|` has entries
`x i * conj (y j)`, and so does `x ⊗ conj y`.

NOTE the codomain: `EuclideanSpace ℂ (m × n)`, not `m × n → ℂ`.  Mathlib's
default `Pi` norm is the sup norm; using it here would make every `‖·‖` in the
development silently wrong.  In this Mathlib `WithLp` is a *structure*, so the
wrapper `WithLp.toLp` is mandatory and a bare function does not even typecheck
-- the mistake is caught by the elaborator rather than by a wrong norm.  Do not
"simplify" this by dropping the wrapper. -/
def vec (A : Matrix m n ℂ) : EuclideanSpace ℂ (m × n) :=
  WithLp.toLp 2 (fun p : m × n => A p.1 p.2)

end Generic

section Bipartite

variable {U V : Type*} [Fintype U] [Fintype V]

/-- `Tr_U C`: the partial trace **over** the factor `U`, leaving an operator on `V`.

PAPER CONVENTION (section 1): "The notation `Tr_U` means the partial trace
*over* the factor `U`."  This is the opposite of the "partial trace *onto*"
convention used in parts of the quantum-information literature; getting it
backwards swaps the two sides of the main inequality, which is symmetric, so
the error would NOT show up in Theorem 1.1 -- it surfaces only in the
asymmetric Theorem 5.9.  Confirmed against `preflight.py`, which tests both. -/
abbrev ptraceU (C : Matrix (U × V) (U × V) ℂ) : Matrix V V ℂ := C.traceLeft

/-- `Tr_V C`: the partial trace **over** the factor `V`, leaving an operator on `U`. -/
abbrev ptraceV (C : Matrix (U × V) (U × V) ℂ) : Matrix U U ℂ := C.traceRight

end Bipartite

/-! ## The imported black box -/

section Skew

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]

/-- `so(U)`: skew-symmetric w.r.t. the fixed orthonormal basis (section 2).

Note this is transposition, NOT conjugate transposition: `Lᵀ = -L`, not
`Lᴴ = -L`.  The whole double-skew argument depends on `K ∈ so(U) ⊗ so(V)`
being *symmetric* (`Kᵀ = K`), which is what makes `⟪ψ, 𝒯c⟫ = 0` in
`eq:T-orthogonal`.  Verified numerically: `preflight.py`, check
"Sec 2  K^T = K for K in so(U)(x)so(V)". -/
def IsSkew (L : Matrix U U ℂ) : Prop := Lᵀ = -L

/-- The double-skew subspace `so(U) ⊗ so(V) ⊆ L(U ⊗ V)`. -/
def doubleSkew (U V : Type*) [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] :
    Submodule ℂ (Matrix (U × V) (U × V) ℂ) :=
  Submodule.span ℂ { K | ∃ L M, IsSkew L ∧ IsSkew M ∧ K = L ⊗ₖ M }

/-- **Interface to Fu-Gao-Park** [arXiv:2607.21367, Thm 2.4], in the exact form
the rest of the paper consumes: this is Lemma 2.1 (`lem:double-skew`),
`eq:double-skew-action`.

The paper derives this from FGP by (i) zero-extending `U, V` to a common `ℂ^d`,
(ii) identifying `vec K ∈ (∧²U) ⊗ (∧²V)`, (iii) applying the best-Schmidt-rank-2
approximation identity, (iv) applying FGP Thm 2.4 with the *crossed* Schmidt cut
`(U_out V_out) : (U_in V_in)`, (v) applying Ky Fan.

Steps (iii) and (v) need theorems Mathlib does not have (PLAN.md gap E);
step (iv) is the index-matching against an external paper (PLAN.md tier D3).

STATUS: the *statement* is numerically confirmed (`preflight.py`, check
"Lem 2.1", tight at 0.500000 for dU,dV in {2,3}).  The *derivation* above is
NOT confirmed by anything -- a numerical check cannot distinguish a valid
derivation from an invalid derivation of a true statement.  Tier D3 is open. -/
def DoubleSkewBound (U V : Type*)
    [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] : Prop :=
  ∀ K ∈ doubleSkew U V, ∀ x y : EuclideanSpace ℂ (U × V),
    ‖x‖ = 1 → ‖y‖ = 1 → inner ℂ x y = 0 →
      ‖Matrix.toEuclideanLin K x‖ ^ 2 + ‖Matrix.toEuclideanLin K y‖ ^ 2
        ≤ hsNormSq K / 2

/-! ## The main theorem -/

/-- **Theorem 1.1** (`thm:rank_r`).  For `C` of rank at most `r`,
`‖Tr_U C‖₂² + ‖Tr_V C‖₂² ≤ r ‖C‖₂² + (1/r) |Tr C|²`.

`hFGP` is the Fu-Gao-Park import, carried as a hypothesis rather than an
`axiom` so that `#print axioms` stays a meaningful hygiene check and the
dependency on an unreviewed preprint is visible in the type. -/
theorem rank_r_partial_trace (hFGP : DoubleSkewBound U V)
    (C : Matrix (U × V) (U × V) ℂ) (r : ℕ) (hr : 0 < r) (hrank : C.rank ≤ r) :
    hsNormSq (ptraceU C) + hsNormSq (ptraceV C)
      ≤ r * hsNormSq C + (1 / r : ℝ) * Complex.normSq C.trace := by
  sorry

/-
NOT YET STATED: **Proposition 2.2** (`prop:operator_ineq`), the load-bearing
step `H_r ⪰ 0`, where

  H_r = I_{UVQ} + (1/r) ρ - ρ_{UQ} ⊗ I_V - I_U ⊗ ρ_{VQ}.

Stating it requires the `U ⊗ V ⊗ Q` operator layer (the marginals `ρ_UQ`,
`ρ_VQ` and the factor-placement reindexing of `eq:Phi-expansion`), which does
not exist yet.  Deliberately left as a comment rather than a `theorem ... : True`
stub: a vacuous statement carrying a `sorry` looks like progress on Prop 2.2
while proving nothing about it, and could be closed by `trivial` without anyone
noticing.  This is tier D2 in PLAN.md -- the complete-graph Cauchy-Schwarz and
the `ran 𝒯 ⊥ ψ` argument are where a real error would hide.
-/

end Skew

end RankR
