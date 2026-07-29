/-
Entrywise complex conjugation of Euclidean vectors.

The operation is used throughout the matrix and amplification developments, as
is the fact that it preserves orthonormal families.
-/
import RankR.Library.Matrix.Elementary

namespace RankR

open Matrix ComplexConjugate

section Conjugate

variable {W : Type*}

/-- The entrywise complex conjugate of a vector. -/
def bar (w : EuclideanSpace ℂ W) : EuclideanSpace ℂ W :=
  WithLp.toLp 2 (fun p => conj (w p))

@[simp] theorem bar_apply (w : EuclideanSpace ℂ W) (p : W) : bar w p = conj (w p) := rfl

variable [Fintype W]

/-- Entrywise complex conjugation preserves orthonormality. -/
theorem orthonormal_conj {ι : Type*} {e : ι → EuclideanSpace ℂ W} (he : Orthonormal ℂ e) :
    Orthonormal ℂ (fun i => bar (e i)) := by
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

omit [Fintype W] in
/-- `(|x⟩⟨y|)ᵀ = |ȳ⟩⟨x̄|`. -/
theorem transpose_rankOne (x y : EuclideanSpace ℂ W) :
    (rankOne x y)ᵀ = rankOne (bar y) (bar x) := by
  ext p q
  simp [rankOne, Matrix.transpose_apply, mul_comm]

/-- Entrywise conjugation is an isometry. -/
theorem norm_bar (v : EuclideanSpace ℂ W) :
    ‖bar v‖ = ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  exact congrArg _ (Finset.sum_congr rfl fun p _ => by simp)

end Conjugate

end RankR
