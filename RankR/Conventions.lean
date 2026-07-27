/-
Conventions for the formalization of

  E. Gershuni, "A Sharp Rank-r Partial-Trace Inequality via Double-Skew
  Singular-Value Bounds" (rank-r.tex, July 2026)

This file pins down every convention fixed in section 1 of the paper, states the
main theorem, and states the interface to the one imported result
(Fu-Gao-Park, arXiv:2607.21367, Thm 2.4).

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

Defined by hand: Mathlib exposes the Frobenius norm only through a scoped,
non-instance definition and has no Frobenius `InnerProductSpace`.  The bridge
to Mathlib's `EuclideanSpace`, from which Cauchy-Schwarz and positivity follow,
is `RankR.hsNormSq_eq_norm_sq`. -/
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
asymmetric Theorem 5.9. -/
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
`eq:T-orthogonal`. -/
def IsSkew (L : Matrix U U ℂ) : Prop := Lᵀ = -L

/-- The double-skew subspace `so(U) ⊗ so(V) ⊆ L(U ⊗ V)`.

This is the linear *span* of the elementary tensors `L ⊗ M`, not the set of
elementary tensors: `eq:T-definition` applies the double-skew bound to
`∑_{α,β} c_{αβ} L_α ⊗ M_β`, a general element. -/
def doubleSkew (U V : Type*) [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] :
    Submodule ℂ (Matrix (U × V) (U × V) ℂ) :=
  Submodule.span ℂ { K | ∃ L M, IsSkew L ∧ IsSkew M ∧ K = L ⊗ₖ M }

/-- **Interface to Fu-Gao-Park** [arXiv:2607.21367, Thm 2.4], in the exact form
the rest of the paper consumes: this is Lemma 2.1 (`lem:double-skew`),
`eq:double-skew-action`.

The paper derives this from FGP by zero-extending `U, V` into a common `ℂ^d`,
identifying `vec K ∈ (∧²U) ⊗ (∧²V)`, applying the best-Schmidt-rank-2
approximation identity, applying FGP Thm 2.4 with the crossed Schmidt cut
`(U_out V_out) : (U_in V_in)`, and applying Ky Fan.  That derivation is not
formalized here; the bound is taken as a hypothesis.

Carried as a hypothesis rather than an `axiom`, so that `#print axioms` on
anything downstream remains meaningful and the dependency is visible in the
type. -/
def DoubleSkewBound (U V : Type*)
    [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] : Prop :=
  ∀ K ∈ doubleSkew U V, ∀ x y : EuclideanSpace ℂ (U × V),
    ‖x‖ = 1 → ‖y‖ = 1 → inner ℂ x y = 0 →
      ‖Matrix.toEuclideanLin K x‖ ^ 2 + ‖Matrix.toEuclideanLin K y‖ ^ 2
        ≤ hsNormSq K / 2

end Skew

end RankR
