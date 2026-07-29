/-
Kraus-style sums and positivity.

A Kraus sum `Y ↦ ∑ₐ Kₐ Y Kₐᴴ` acts on quadratic forms by pulling the test
vector back through each `Kₐᴴ`.  Since the pullback only moves the vector, a
matrix whose quadratic form has nonnegative real part is sent to another such
matrix; positive semidefiniteness is preserved.
-/
import RankR.Library.Matrix.Action

namespace RankR

open Matrix Finset ComplexConjugate

section Kraus

variable {W : Type*} [Fintype W]

/-- The Kraus sum `Y ↦ ∑ₐ Kₐ Y Kₐᴴ` with Kraus operators `K`. -/
def krausSum {ι : Type*} [Fintype ι] (K : ι → Matrix W W ℂ) (Y : Matrix W W ℂ) :
    Matrix W W ℂ := ∑ a, K a * Y * (K a)ᴴ

/-- The quadratic form of a Kraus sum is the sum of the quadratic forms of `Y`
at the pullbacks of the test vector through the `Kₐᴴ`. -/
theorem qform_krausSum {ι : Type*} [Fintype ι] (K : ι → Matrix W W ℂ)
    (Y : Matrix W W ℂ) (x : EuclideanSpace ℂ W) :
    qform (krausSum K Y) x = ∑ a, qform Y (mulVecE (K a)ᴴ x) := by
  rw [krausSum, qform_sum]
  exact Finset.sum_congr rfl fun a _ => qform_conj (K a) Y x

/-- A Kraus sum preserves positive semidefiniteness. -/
theorem qform_krausSum_nonneg {ι : Type*} [Fintype ι] (K : ι → Matrix W W ℂ)
    {Y : Matrix W W ℂ} (hY : ∀ z : EuclideanSpace ℂ W, 0 ≤ (qform Y z).re)
    (x : EuclideanSpace ℂ W) : 0 ≤ (qform (krausSum K Y) x).re := by
  rw [qform_krausSum, Complex.re_sum]
  exact Finset.sum_nonneg fun a _ => hY _

/-- Rank-one projectors are positive semidefinite. -/
theorem qform_rankOne_nonneg (y x : EuclideanSpace ℂ W) : 0 ≤ (qform (rankOne y y) x).re := by
  rw [qform_rankOne, Complex.ofReal_re]
  exact Complex.normSq_nonneg _

end Kraus

end RankR
