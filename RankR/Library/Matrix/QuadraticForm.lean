/-
Quadratic forms of finite complex matrices.
-/
import RankR.Library.Matrix.Elementary
import Mathlib.Analysis.Matrix.Order

namespace RankR

open Matrix Finset ComplexConjugate
open scoped ComplexOrder

variable {W : Type*} [Fintype W]

/-- The quadratic form `⟪x, A x⟫`, written in finite coordinates. -/
def qform (A : Matrix W W ℂ) (x : EuclideanSpace ℂ W) : ℂ :=
  ∑ p, ∑ q, conj (x p) * A p q * x q

theorem qform_add (A B : Matrix W W ℂ) (x : EuclideanSpace ℂ W) :
    qform (A + B) x = qform A x + qform B x := by
  simp only [qform, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem qform_sub (A B : Matrix W W ℂ) (x : EuclideanSpace ℂ W) :
    qform (A - B) x = qform A x - qform B x := by
  simp only [qform, Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]

theorem qform_smul (c : ℂ) (A : Matrix W W ℂ) (x : EuclideanSpace ℂ W) :
    qform (c • A) x = c * qform A x := by
  simp only [qform, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring

/-- Scaling the tested vector scales its quadratic form by the scalar's squared norm. -/
theorem qform_smul_vec (A : Matrix W W ℂ) (c : ℂ)
    (x : EuclideanSpace ℂ W) :
    qform A (c • x) = (Complex.normSq c : ℂ) * qform A x := by
  simp only [qform, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, map_mul,
    Complex.normSq_eq_conj_mul_self, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- The quadratic form is additive over a finite matrix sum. -/
theorem qform_sum_finset {ι : Type*} (t : Finset ι) (A : ι → Matrix W W ℂ)
    (x : EuclideanSpace ℂ W) : qform (∑ a ∈ t, A a) x = ∑ a ∈ t, qform (A a) x := by
  simp only [qform, Matrix.sum_apply, Finset.mul_sum, Finset.sum_mul]
  exact Eq.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_comm) Finset.sum_comm

/-- The quadratic form is additive over a `Fintype`-indexed matrix sum. -/
theorem qform_sum {ι : Type*} [Fintype ι] (A : ι → Matrix W W ℂ) (x : EuclideanSpace ℂ W) :
    qform (∑ a, A a) x = ∑ a, qform (A a) x := qform_sum_finset _ A x

/-- `⟪x, I x⟫ = ‖x‖²`. -/
theorem qform_one [DecidableEq W] (x : EuclideanSpace ℂ W) :
    qform (1 : Matrix W W ℂ) x = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  have h : qform (1 : Matrix W W ℂ) x = ∑ p, conj (x p) * x p := by
    simp only [qform, Matrix.one_apply, mul_ite, ite_mul, mul_one, mul_zero,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [h, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  push_cast
  exact Finset.sum_congr rfl fun p _ => by
    rw [← Complex.normSq_eq_conj_mul_self]
    simp [Complex.normSq_eq_norm_sq]

/-- `⟪x, |y⟩⟨y| x⟫ = |⟪y, x⟫|²`. -/
theorem qform_rankOne (y x : EuclideanSpace ℂ W) :
    qform (rankOne y y) x = ((Complex.normSq (inner ℂ y x) : ℝ) : ℂ) := by
  have h : qform (rankOne y y) x
      = (∑ p, conj (x p) * y p) * (∑ q, conj (y q) * x q) := by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by
      simp [rankOne]; ring
  rw [h]
  have h1 : (∑ q, conj (y q) * x q) = inner ℂ y x := by
    rw [PiLp.inner_apply]
    exact Finset.sum_congr rfl fun q _ => (RCLike.inner_apply' (y q) (x q)).symm
  have h2 : (∑ p, conj (x p) * y p) = conj (inner ℂ y x) := by
    rw [PiLp.inner_apply, map_sum]
    exact Finset.sum_congr rfl fun p _ => by
      rw [RCLike.inner_apply', map_mul, Complex.conj_conj]; ring
  rw [h1, h2, Complex.normSq_eq_conj_mul_self]

/-- Positive semidefiniteness implies nonnegativity of the real quadratic
form. -/
theorem qform_re_nonneg_of_posSemidef
    {A : Matrix W W ℂ} (hA : A.PosSemidef) (x : EuclideanSpace ℂ W) :
    0 ≤ (qform A x).re := by
  have hq : 0 ≤ qform A x := by
    have h := hA.dotProduct_mulVec_nonneg (x : W → ℂ)
    simpa [qform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc] using h
  exact (Complex.nonneg_iff.mp hq).1

end RankR
