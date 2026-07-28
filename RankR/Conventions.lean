/-
Conventions for the formalization of

  E. Gershuni, "A Sharp Rank-r Partial-Trace Inequality via Double-Skew
  Singular-Value Bounds" (rank-r.tex, July 2026)

This file pins down every convention fixed in section 1 of the paper, states the
main theorem, and states the interface to the one imported result
(Fu-Gao-Park, arXiv:2607.21367, Thm 2.4).

Sections are split by which instances each declaration needs.  Lean's `variable`
inclusion heuristic pulls in every instance-implicit whose type mentions an
included variable, so a single omnibus `variable` line would give `vec` a
spurious `[DecidableEq m]` argument.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Kronecker

namespace RankR

open Matrix ComplexConjugate
open scoped Kronecker

/-! ## Section 1 conventions -/

section Generic

variable {m n : Type*} [Fintype m] [Fintype n]

/-- Hilbert-Schmidt inner product `⟪A, B⟫ = Tr(Aᴴ B)`.

Section 1 of the paper takes inner products conjugate-linear in the first
argument and linear in the second, which is also Mathlib's convention for
`⟪·,·⟫_ℂ`; no flip is needed anywhere.  The choice is what fixes which of
`Tr C` and `conj (Tr C)` appears throughout section 3. -/
noncomputable def hsInner (A B : Matrix m n ℂ) : ℂ := (Aᴴ * B).trace

/-- `‖A‖₂²`, the squared Hilbert-Schmidt (Schatten-2, Frobenius) norm.

Mathlib exposes the Frobenius norm only through a scoped, non-instance
definition and has no Frobenius `InnerProductSpace`, so this is defined
directly.  The bridge
to Mathlib's `EuclideanSpace`, from which Cauchy-Schwarz and positivity follow,
is `RankR.hsNormSq_eq_norm_sq`. -/
def hsNormSq (A : Matrix m n ℂ) : ℝ := ∑ i, ∑ j, Complex.normSq (A i j)

/-- Vectorization, normalized by `vec (|x⟩⟨y|) = x ⊗ conj y` (section 1).

On entries this is the identity: `|x⟩⟨y|` has entries `x i * conj (y j)`, and
so does `x ⊗ conj y`.

The codomain is `EuclideanSpace ℂ (m × n)`, not `m × n → ℂ`: the `Pi` norm is
the sup norm, whereas every `‖·‖` in this development is the Hilbert-Schmidt
norm.  `EuclideanSpace` is a `WithLp` structure, so the `WithLp.toLp` wrapper
is part of the definition. -/
def vec (A : Matrix m n ℂ) : EuclideanSpace ℂ (m × n) :=
  WithLp.toLp 2 (fun p : m × n => A p.1 p.2)

end Generic

section Bipartite

variable {U V : Type*} [Fintype U] [Fintype V]

/-- `Tr_U C`: the partial trace **over** the factor `U`, leaving an operator on `V`.

Section 1 of the paper takes `Tr_U` to mean the partial trace *over* the
factor `U`, the opposite of the "partial trace *onto*" convention used in parts
of the quantum-information literature.  The two readings differ by exchanging
the sides of Theorem 1.1, which is symmetric in them; they are distinguishable
only in the asymmetric Theorem 5.9. -/
abbrev ptraceU (C : Matrix (U × V) (U × V) ℂ) : Matrix V V ℂ :=
  Matrix.of fun b c => ∑ a, C (a, b) (a, c)

/-- `Tr_V C`: the partial trace **over** the factor `V`, leaving an operator on `U`. -/
abbrev ptraceV (C : Matrix (U × V) (U × V) ℂ) : Matrix U U ℂ :=
  Matrix.of fun a a' => ∑ b, C (a, b) (a', b)

end Bipartite

/-! ## The imported black box -/

section Skew

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]

/-- `so(U)`: skew-symmetric w.r.t. the fixed orthonormal basis (section 2).

This is transposition rather than conjugate transposition: `Lᵀ = -L`, not
`Lᴴ = -L`.  The double-skew argument rests on `K ∈ so(U) ⊗ so(V)` being
*symmetric* (`Kᵀ = K`), which is what makes `⟪ψ, 𝒯c⟫ = 0` in
`eq:T-orthogonal`. -/
def IsSkew (L : Matrix U U ℂ) : Prop := Lᵀ = -L

/-- The double-skew subspace `so(U) ⊗ so(V) ⊆ L(U ⊗ V)`.

This is the linear *span* of the elementary tensors `L ⊗ M`, not the set of
elementary tensors: `eq:T-definition` applies the double-skew bound to
`∑_{α,β} c_{αβ} L_α ⊗ M_β`, a general element. -/
def doubleSkew (U V : Type*) [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] :
    Submodule ℂ (Matrix (U × V) (U × V) ℂ) :=
  Submodule.span ℂ { K | ∃ L M, IsSkew L ∧ IsSkew M ∧ K = L ⊗ₖ M }

/-- **The double-skew action bound**, Lemma 2.1 of the paper
(`lem:double-skew`, `eq:double-skew-action`): on the double-skew subspace, the
action on an orthonormal pair is at most half the squared Hilbert-Schmidt norm.

A `Prop` rather than an `axiom`, so the dependency is visible in the type of
every result that uses it and `#print axioms` stays meaningful.
`RankR.doubleSkewBound_of_FGP` derives it from the Fu-Gao-Park estimate. -/
def DoubleSkewBound (U V : Type*)
    [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] : Prop :=
  ∀ K ∈ doubleSkew U V, ∀ x y : EuclideanSpace ℂ (U × V),
    ‖x‖ = 1 → ‖y‖ = 1 → inner ℂ x y = 0 →
      ‖Matrix.toEuclideanLin K x‖ ^ 2 + ‖Matrix.toEuclideanLin K y‖ ^ 2
        ≤ hsNormSq K / 2

end Skew

end RankR
