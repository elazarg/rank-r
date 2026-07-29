/-
Restricted operator norms on vectors of bounded pure Schmidt rank.

The value set follows the manuscript definition: normalized vectors of pure
Schmidt rank at most `k`.  Zero is adjoined so the definition remains total in
zero-dimensional coordinate spaces; it does not affect positive Choi
operators.
-/
import RankR.Library.Quantum.Choi

namespace RankR

open Matrix

section SchmidtOperatorNorm

variable {W : Type*} [Fintype W]

noncomputable local instance schmidtOperatorNormDecidableEq :
    DecidableEq W := Classical.decEq W

/-- Quadratic-form values on normalized vectors of pure Schmidt rank at most
`k`, together with zero. -/
def schmidtOperatorValues
    (J : Matrix (W × W) (W × W) ℂ) (k : ℕ) : Set ℝ :=
  {0} ∪ {x | ∃ z : EuclideanSpace ℂ (W × W),
    ‖z‖ = 1 ∧ pureSchmidtRank z ≤ k ∧ x = (qform J z).re}

/-- The restricted `S(k)` operator norm in finite coordinates. -/
noncomputable def schmidtOperatorNorm
    (J : Matrix (W × W) (W × W) ℂ) (k : ℕ) : ℝ :=
  sSup (schmidtOperatorValues J k)

theorem schmidtOperatorValues_nonempty
    (J : Matrix (W × W) (W × W) ℂ) (k : ℕ) :
    (schmidtOperatorValues J k).Nonempty :=
  ⟨0, Set.mem_union_left _ (Set.mem_singleton 0)⟩

theorem schmidtOperatorValues_bddAbove
    (J : Matrix (W × W) (W × W) ℂ) (k : ℕ) :
    BddAbove (schmidtOperatorValues J k) := by
  let T := (Matrix.toEuclideanLin J).toContinuousLinearMap
  refine ⟨‖T‖, ?_⟩
  intro x hx
  rcases hx with hx | hx
  · have hx0 : x = 0 := Set.mem_singleton_iff.mp hx
    rw [hx0]
    exact norm_nonneg T
  · obtain ⟨z, hz, -, rfl⟩ := hx
    calc
      (qform J z).re ≤ ‖qform J z‖ := Complex.re_le_norm _
      _ = ‖inner ℂ z (Matrix.toEuclideanLin J z)‖ := by
        rw [qform_eq_inner, mulVecE_eq_toEuclideanLin]
      _ ≤ ‖z‖ * ‖Matrix.toEuclideanLin J z‖ :=
        norm_inner_le_norm _ _
      _ ≤ ‖z‖ * (‖T‖ * ‖z‖) :=
        mul_le_mul_of_nonneg_left (T.le_opNorm z) (norm_nonneg z)
      _ = ‖T‖ := by rw [hz]; ring

/-- The restricted operator norm is nonnegative. -/
theorem schmidtOperatorNorm_nonneg
    (J : Matrix (W × W) (W × W) ℂ) (k : ℕ) :
    0 ≤ schmidtOperatorNorm J k := by
  apply le_csSup (schmidtOperatorValues_bddAbove J k)
  exact Set.mem_union_left _ (Set.mem_singleton 0)

/-- Homogeneous form of the restricted operator-norm bound. -/
theorem re_qform_le_schmidtOperatorNorm_mul_norm_sq
    (J : Matrix (W × W) (W × W) ℂ) (k : ℕ)
    (z : EuclideanSpace ℂ (W × W)) (hrank : pureSchmidtRank z ≤ k) :
    (qform J z).re ≤ schmidtOperatorNorm J k * ‖z‖ ^ 2 := by
  rcases eq_or_ne z 0 with rfl | hz0
  · simp [qform]
  · let c : ℂ := ((‖z‖ : ℝ) : ℂ)⁻¹
    let zn : EuclideanSpace ℂ (W × W) := c • z
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have hc : c ≠ 0 := by
      exact inv_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hzpos))
    have hznorm : ‖zn‖ = 1 := by
      simp [zn, c, norm_smul, hzpos.ne']
    have hznrank : pureSchmidtRank zn ≤ k := by
      change pureSchmidtRank (c • z) ≤ k
      rw [pureSchmidtRank_smul_of_ne_zero _ hc]
      exact hrank
    have hmem :
        (qform J zn).re ∈ schmidtOperatorValues J k :=
      Set.mem_union_right _ ⟨zn, hznorm, hznrank, rfl⟩
    have hle :
        (qform J zn).re ≤ schmidtOperatorNorm J k :=
      le_csSup (schmidtOperatorValues_bddAbove J k) hmem
    have hcnormSq : Complex.normSq c = (‖z‖ ^ 2)⁻¹ := by
      simp [c, Complex.normSq_ofReal]
      ring
    have hscale :
        (qform J zn).re = (‖z‖ ^ 2)⁻¹ * (qform J z).re := by
      change (qform J (c • z)).re =
        (‖z‖ ^ 2)⁻¹ * (qform J z).re
      rw [qform_smul_vec, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, hcnormSq]
    rw [hscale] at hle
    calc
      (qform J z).re =
          ((‖z‖ ^ 2)⁻¹ * (qform J z).re) * ‖z‖ ^ 2 := by
            field_simp [ne_of_gt hzpos]
      _ ≤ schmidtOperatorNorm J k * ‖z‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hle (sq_nonneg ‖z‖)

/-- A homogeneous pure-Schmidt-rank bound is equivalent to an upper bound on
the restricted operator norm. -/
theorem pureSchmidtKBound_iff_schmidtOperatorNorm_le
    {J : Matrix (W × W) (W × W) ℂ} {k : ℕ} {β : ℝ}
    (hβ : 0 ≤ β) :
    PureSchmidtKBound J k β ↔
      schmidtOperatorNorm J k ≤ (k : ℝ) * β := by
  constructor
  · intro h
    apply csSup_le (schmidtOperatorValues_nonempty J k)
    intro x hx
    rcases hx with hx | hx
    · have hx0 : x = 0 := Set.mem_singleton_iff.mp hx
      rw [hx0]
      exact mul_nonneg (Nat.cast_nonneg k) hβ
    · obtain ⟨z, hz, hrank, rfl⟩ := hx
      have hzbound := h z hrank
      rw [hz, one_pow, mul_one] at hzbound
      exact hzbound
  · intro h z hrank
    exact (re_qform_le_schmidtOperatorNorm_mul_norm_sq J k z hrank).trans
      (mul_le_mul_of_nonneg_right h (sq_nonneg ‖z‖))

/-- The rank-two Choi bound is exactly an upper bound on the `S(2)` norm. -/
theorem choiTwoBound_iff_schmidtOperatorNorm_le
    {J : Matrix (W × W) (W × W) ℂ} {β : ℝ}
    (hβ : 0 ≤ β) :
    ChoiTwoBound J β ↔ schmidtOperatorNorm J 2 ≤ 2 * β := by
  rw [choiTwoBound_iff_pureSchmidtKBound_two,
    pureSchmidtKBound_iff_schmidtOperatorNorm_le hβ]
  norm_num

/-- Half of the `S(2)` norm, the local constant used by pair lifting. -/
noncomputable def betaTwo
    (J : Matrix (W × W) (W × W) ℂ) : ℝ :=
  (1 / 2 : ℝ) * schmidtOperatorNorm J 2

theorem betaTwo_nonneg
    (J : Matrix (W × W) (W × W) ℂ) :
    0 ≤ betaTwo J :=
  mul_nonneg (by norm_num) (schmidtOperatorNorm_nonneg J 2)

/-- A nonnegative scalar is a valid rank-two Choi constant exactly when it
dominates `betaTwo`. -/
theorem choiTwoBound_iff_betaTwo_le
    {J : Matrix (W × W) (W × W) ℂ} {β : ℝ}
    (hβ : 0 ≤ β) :
    ChoiTwoBound J β ↔ betaTwo J ≤ β := by
  rw [choiTwoBound_iff_schmidtOperatorNorm_le hβ, betaTwo]
  constructor <;> intro h <;> nlinarith

/-- `betaTwo` itself satisfies the rank-two Choi bound. -/
theorem choiTwoBound_betaTwo
    (J : Matrix (W × W) (W × W) ℂ) :
    ChoiTwoBound J (betaTwo J) :=
  (choiTwoBound_iff_betaTwo_le (betaTwo_nonneg J)).mpr le_rfl

end SchmidtOperatorNorm

end RankR
