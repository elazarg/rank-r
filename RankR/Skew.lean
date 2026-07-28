/-
Groundwork for the double-skew subspace `so(U) ⊗ so(V)` of section 2.

Three independent pieces, all of them structural rather than quantitative:

* the elementary skew-symmetric matrices `skewUnit a b = E_{ab} - E_{ba}`, which
  span `so(W)` and supply the concrete generators fed to `doubleSkew`;
* the closure properties of `doubleSkew U V` under the sums and scalar multiples
  that `eq:T-definition` forms, together with the symmetry `Kᵀ = K` enjoyed by
  every element of it -- the sign cancellation `(-L) ⊗ₖ (-M) = L ⊗ₖ M` is exactly
  what makes the *skew* hypothesis produce a *symmetric* operator;
* invariance of orthonormality under entrywise complex conjugation, which is what
  lets the conjugate of a basis be used as a basis.
-/
import RankR.Conventions

namespace RankR

open Matrix Finset ComplexConjugate
open scoped Kronecker

/-! ## Elementary skew-symmetric matrices -/

section SkewUnits

variable {W : Type*} [DecidableEq W]

/-- The elementary skew-symmetric matrix `E_{ab} - E_{ba}`.

For `a = b` this is the zero matrix; for `a ≠ b` it is the generator of the
rotation in the `(a, b)` plane.  These matrices span `so(W)`. -/
def skewUnit (a b : W) : Matrix W W ℂ := Matrix.single a b 1 - Matrix.single b a 1

/-- The entries of `skewUnit a b` as a difference of products of Kronecker
deltas. -/
theorem skewUnit_apply (a b p q : W) :
    skewUnit a b p q
      = (if a = p then (1 : ℂ) else 0) * (if b = q then 1 else 0)
        - (if b = p then (1 : ℂ) else 0) * (if a = q then 1 else 0) := by
  simp only [skewUnit, Matrix.sub_apply, Matrix.single_apply, ite_and, ite_mul,
    one_mul, zero_mul]

/-- `skewUnit a b` is skew-symmetric: `(E_{ab} - E_{ba})ᵀ = E_{ba} - E_{ab}`. -/
theorem skewUnit_isSkew (a b : W) : IsSkew (skewUnit a b) := by
  rw [IsSkew, skewUnit, Matrix.transpose_sub, Matrix.transpose_single,
    Matrix.transpose_single, neg_sub]

end SkewUnits

/-! ## Conjugation and orthonormality

Independent of the skew units: what is needed of conjugation is that it is an
isometry, which is a statement about the index type alone. -/

section Conj

variable {W : Type*} [Fintype W]

/-- Entrywise complex conjugation preserves orthonormality.

Conjugation is an isometry of `ℂ` and conjugates the Hermitian form,
`⟪conj x, conj y⟫ = conj ⟪x, y⟫`, so it fixes norms and preserves vanishing of
inner products. -/
theorem orthonormal_conj {ι : Type*} {e : ι → EuclideanSpace ℂ W} (he : Orthonormal ℂ e) :
    Orthonormal ℂ (fun i => (WithLp.toLp 2 (fun p => conj (e i p)) : EuclideanSpace ℂ W)) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · rw [EuclideanSpace.norm_eq, ← he.1 i, EuclideanSpace.norm_eq]
    exact congrArg _ (Finset.sum_congr rfl fun p _ => by simp)
  · have h : inner ℂ (e i) (e j) = 0 := he.2 hij
    rw [PiLp.inner_apply] at h
    have h' := congrArg (starRingEnd ℂ) h
    rw [map_sum, map_zero] at h'
    show inner ℂ _ _ = (0 : ℂ)
    rw [PiLp.inner_apply, ← h']
    exact Finset.sum_congr rfl fun p _ => by simp [mul_comm]

end Conj

/-! ## The double-skew subspace -/

section DoubleSkew

variable {U V : Type*}

/-- Elementary tensors of skew matrices are the generators of `doubleSkew`. -/
theorem kron_mem_doubleSkew {L : Matrix U U ℂ} {M : Matrix V V ℂ}
    (hL : IsSkew L) (hM : IsSkew M) : L ⊗ₖ M ∈ doubleSkew U V :=
  Submodule.subset_span ⟨L, M, hL, hM, rfl⟩

/-- The general element `∑_{α,β} c_{αβ} L_α ⊗ M_β` of `eq:T-definition` lies in
`doubleSkew`, since a submodule is closed under scalar multiples and finite sums. -/
theorem sum_smul_kron_mem_doubleSkew {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → κ → ℂ) (L : ι → Matrix U U ℂ) (M : κ → Matrix V V ℂ)
    (hL : ∀ i, IsSkew (L i)) (hM : ∀ j, IsSkew (M j)) :
    ∑ i, ∑ j, c i j • (L i ⊗ₖ M j) ∈ doubleSkew U V :=
  Submodule.sum_mem _ fun i _ =>
    Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (kron_mem_doubleSkew (hL i) (hM j))

/-- Every element of `so(U) ⊗ so(V)` is a *symmetric* matrix.

On a generator the two minus signs cancel,
`(L ⊗ₖ M)ᵀ = Lᵀ ⊗ₖ Mᵀ = (-L) ⊗ₖ (-M) = L ⊗ₖ M`,
and symmetry is preserved by the zero matrix, sums and scalar multiples, so it
propagates to the whole span.  This is the input to `eq:T-orthogonal`. -/
theorem transpose_eq_self_of_mem_doubleSkew {K : Matrix (U × V) (U × V) ℂ}
    (hK : K ∈ doubleSkew U V) : Kᵀ = K := by
  rw [doubleSkew] at hK
  induction hK using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨L, M, hL, hM, rfl⟩ := hx
      rw [← Matrix.kroneckerMap_transpose, hL, hM]
      ext p q
      simp
  | zero => exact Matrix.transpose_zero
  | add x y _ _ hx hy => rw [Matrix.transpose_add, hx, hy]
  | smul a x _ hx => rw [Matrix.transpose_smul, hx]

end DoubleSkew

end RankR
