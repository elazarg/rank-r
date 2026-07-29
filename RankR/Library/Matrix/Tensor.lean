/-
Hilbert--Schmidt and partial-trace identities for tensor products.
-/
import RankR.Library.Matrix.Elementary

namespace RankR

open Matrix Finset ComplexConjugate
open scoped Kronecker

section PartialTrace

variable {U V : Type*} [Fintype U] [Fintype V]

/-- Taking the partial trace over the second factor preserves the full trace. -/
theorem trace_ptraceV (C : Matrix (U × V) (U × V) ℂ) :
    (ptraceV C).trace = C.trace := by
  simp [Matrix.trace, Fintype.sum_prod_type]

/-- Taking the partial trace over the first factor preserves the full trace. -/
theorem trace_ptraceU (C : Matrix (U × V) (U × V) ℂ) :
    (ptraceU C).trace = C.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, ptraceU_apply, Fintype.sum_prod_type]
  exact Finset.sum_comm

omit [Fintype U] in
theorem ptraceV_add (A B : Matrix (U × V) (U × V) ℂ) :
    ptraceV (A + B) = ptraceV A + ptraceV B := by
  ext i j
  simp [Finset.sum_add_distrib]

omit [Fintype U] in
theorem ptraceV_smul (c : ℂ) (A : Matrix (U × V) (U × V) ℂ) :
    ptraceV (c • A) = c • ptraceV A := by
  ext i j
  simp [Finset.mul_sum]

omit [Fintype V] in
theorem ptraceU_add (A B : Matrix (U × V) (U × V) ℂ) :
    ptraceU (A + B) = ptraceU A + ptraceU B := by
  ext i j
  simp [Finset.sum_add_distrib]

omit [Fintype V] in
theorem ptraceU_smul (c : ℂ) (A : Matrix (U × V) (U × V) ℂ) :
    ptraceU (c • A) = c • ptraceU A := by
  ext i j
  simp [Finset.mul_sum]

omit [Fintype U] in
/-- The partial trace of a Kronecker product contracts its second factor. -/
theorem ptraceV_kronecker
    (A : Matrix U U ℂ) (B : Matrix V V ℂ) :
    ptraceV (A ⊗ₖ B) = B.trace • A := by
  ext i j
  simp only [ptraceV_apply, Matrix.kroneckerMap_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.trace, Matrix.diag_apply]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring

omit [Fintype V] in
/-- The partial trace of a Kronecker product contracts its first factor. -/
theorem ptraceU_kronecker
    (A : Matrix U U ℂ) (B : Matrix V V ℂ) :
    ptraceU (A ⊗ₖ B) = A.trace • B := by
  ext i j
  simp only [ptraceU_apply, Matrix.kroneckerMap_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.trace, Matrix.diag_apply]
  rw [Finset.sum_mul]

end PartialTrace

section Identity

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The identity is the trace functional in the first Hilbert--Schmidt slot. -/
theorem hsInner_one_left (X : Matrix D D ℂ) :
    hsInner (1 : Matrix D D ℂ) X = X.trace := by
  simp [hsInner]

/-- The identity is the conjugate trace functional in the second
Hilbert--Schmidt slot. -/
theorem hsInner_one_right (X : Matrix D D ℂ) :
    hsInner X (1 : Matrix D D ℂ) = conj X.trace := by
  simp [hsInner, Matrix.trace_conjTranspose, RCLike.star_def]

end Identity

end RankR
