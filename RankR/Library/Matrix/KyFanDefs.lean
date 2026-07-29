/-
Rank-constrained Frobenius tests and squared Ky Fan sums.

The definitions are separated from the spectral proof so applications may
state bounds through the Frobenius-dual interface without importing that
proof.
-/
import RankR.Library.Matrix.Rank
import Mathlib.Analysis.InnerProductSpace.SingularValues

namespace RankR

open Matrix

/-- Ordinary Hilbert--Schmidt Cauchy--Schwarz for matrices. -/
theorem normSq_hsInner_le {m n : Type*} [Fintype m] [Fintype n]
    (X Y : Matrix m n ℂ) :
    Complex.normSq (hsInner X Y) ≤ hsNormSq X * hsNormSq Y := by
  rw [hsInner_eq_inner, Complex.normSq_eq_norm_sq, hsNormSq_eq_norm_sq,
    hsNormSq_eq_norm_sq]
  have h := norm_inner_le_norm (𝕜 := ℂ) (vec X) (vec Y)
  have h₀ : 0 ≤ ‖inner ℂ (vec X) (vec Y)‖ := norm_nonneg _
  have h₁ : 0 ≤ ‖vec X‖ * ‖vec Y‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith

section FrobeniusDuality

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- Squared pairings against rank-at-most-`k`, unit-Frobenius test matrices. -/
def frobeniusRankTestValues (k : ℕ) (M : Matrix W W ℂ) : Set ℝ :=
  {q | ∃ C : Matrix W W ℂ,
    C.rank ≤ k ∧ hsNormSq C ≤ 1 ∧ q = Complex.normSq (hsInner C M)}

/-- The squared rank-`k` Frobenius dual quantity. -/
noncomputable def frobeniusRankTestSq (k : ℕ) (M : Matrix W W ℂ) : ℝ :=
  sSup (frobeniusRankTestValues k M)

theorem frobeniusRankTestValues_nonempty (k : ℕ) (M : Matrix W W ℂ) :
    (frobeniusRankTestValues k M).Nonempty := by
  refine ⟨0, 0, ?_, ?_, ?_⟩
  · simp
  · simp [hsNormSq]
  · simp [hsInner]

omit [DecidableEq W] in
theorem frobeniusRankTestValues_bddAbove (k : ℕ) (M : Matrix W W ℂ) :
    BddAbove (frobeniusRankTestValues k M) := by
  refine ⟨hsNormSq M, ?_⟩
  rintro q ⟨C, -, hnorm, rfl⟩
  calc
    Complex.normSq (hsInner C M) ≤ hsNormSq C * hsNormSq M :=
      normSq_hsInner_le C M
    _ ≤ 1 * hsNormSq M :=
      mul_le_mul_of_nonneg_right hnorm (hsNormSq_nonneg M)
    _ = hsNormSq M := one_mul _

/-- Any homogeneous pointwise rank-`k` bound controls the normalized
Frobenius test supremum. -/
theorem frobeniusRankTestSq_le_of_pointwise {k : ℕ} {M : Matrix W W ℂ}
    {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (h : ∀ C : Matrix W W ℂ, C.rank ≤ k →
      Complex.normSq (hsInner C M) ≤ Λ * hsNormSq C) :
    frobeniusRankTestSq k M ≤ Λ := by
  apply csSup_le (frobeniusRankTestValues_nonempty k M)
  rintro q ⟨C, hrank, hnorm, rfl⟩
  calc
    Complex.normSq (hsInner C M) ≤ Λ * hsNormSq C := h C hrank
    _ ≤ Λ * 1 := mul_le_mul_of_nonneg_left hnorm hΛ
    _ = Λ := mul_one _

/-- The sum of the first `k` squared singular values, using Mathlib's
zero-indexed decreasing singular-value sequence. Singular values beyond the
ambient dimension are zero. -/
noncomputable def kyFanSq (k : ℕ) (M : Matrix W W ℂ) : ℝ :=
  ∑ i ∈ Finset.range k, (Matrix.toEuclideanLin M).singularValues i ^ 2

/-- Frobenius Ky Fan duality for a matrix. -/
def KyFanFrobeniusDuality (k : ℕ) (M : Matrix W W ℂ) : Prop :=
  kyFanSq k M = frobeniusRankTestSq k M

end FrobeniusDuality

end RankR
