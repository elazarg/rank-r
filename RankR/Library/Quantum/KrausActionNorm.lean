/-
The Kraus-action formula for the restricted Schmidt operator norm.

For a finite Kraus family `A`, the `S(k)` norm of its Choi operator is the
supremum of the squared Ky Fan `k`-sums of normalized linear combinations of
the Kraus operators.
-/
import RankR.Library.Matrix.KyFan
import RankR.Library.Quantum.SchmidtOperatorNorm

namespace RankR

open Matrix ComplexConjugate

section KrausActionNorm

variable {W ι : Type*} [Fintype W] [Fintype ι]

noncomputable local instance krausActionNormDecidableEqW :
    DecidableEq W := Classical.decEq W

/-- The linear combination of a Kraus family with Euclidean coefficient
vector `c`. -/
noncomputable def krausCombination
    (A : ι → Matrix W W ℂ) (c : EuclideanSpace ℂ ι) :
    Matrix W W ℂ :=
  ∑ a, c a • A a

/-- Squared Ky Fan `k`-sums of normalized Kraus combinations, together with
zero for the empty coefficient space. -/
def krausActionValues
    (A : ι → Matrix W W ℂ) (k : ℕ) : Set ℝ :=
  {0} ∪ {x | ∃ c : EuclideanSpace ℂ ι,
    ‖c‖ = 1 ∧ x = kyFanSq k (krausCombination A c)}

/-- The supremal squared Ky Fan `k`-sum of a normalized Kraus combination. -/
noncomputable def krausActionNorm
    (A : ι → Matrix W W ℂ) (k : ℕ) : ℝ :=
  sSup (krausActionValues A k)

theorem krausActionValues_nonempty
    (A : ι → Matrix W W ℂ) (k : ℕ) :
    (krausActionValues A k).Nonempty :=
  ⟨0, Set.mem_union_left _ (Set.mem_singleton 0)⟩

/-- Coefficient Cauchy--Schwarz bounds pairing with a Kraus combination by the
Choi quadratic form. -/
theorem normSq_hsInner_krausCombination_le
    (A : ι → Matrix W W ℂ) (c : EuclideanSpace ℂ ι)
    (C : Matrix W W ℂ) :
    Complex.normSq (hsInner C (krausCombination A c)) ≤
      ‖c‖ ^ 2 * (qform (choiOf A) (vec C)).re := by
  let z : EuclideanSpace ℂ ι :=
    WithLp.toLp 2 (fun a => inner ℂ (vec (A a)) (vec C))
  have hpair :
      hsInner C (krausCombination A c) = inner ℂ z c := by
    rw [krausCombination, hsInner_sum_right, PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro a ha
    rw [RCLike.inner_apply', hsInner_smul_right, hsInner_eq_inner,
      inner_conj_symm]
    ring
  have hznorm :
      ‖z‖ ^ 2 = (qform (choiOf A) (vec C)).re := by
    rw [EuclideanSpace.norm_sq_eq, re_qform_choiOf]
    exact Finset.sum_congr rfl fun a _ => by
      rw [Complex.normSq_eq_norm_sq]
  have h := norm_inner_le_norm (𝕜 := ℂ) z c
  have hleft : 0 ≤ ‖inner ℂ z c‖ := norm_nonneg _
  have hright : 0 ≤ ‖z‖ * ‖c‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  rw [hpair, Complex.normSq_eq_norm_sq, ← hznorm]
  nlinarith

/-- Every normalized Kraus combination has squared Ky Fan `k`-sum bounded by
the `S(k)` norm of the Choi operator. -/
theorem kyFanSq_krausCombination_le_schmidtOperatorNorm
    (A : ι → Matrix W W ℂ) (k : ℕ)
    (c : EuclideanSpace ℂ ι) (hc : ‖c‖ = 1) :
    kyFanSq k (krausCombination A c) ≤
      schmidtOperatorNorm (choiOf A) k := by
  rw [kyFanFrobeniusDuality]
  apply frobeniusRankTestSq_le_of_pointwise
    (schmidtOperatorNorm_nonneg (choiOf A) k)
  intro C hrank
  calc
    Complex.normSq (hsInner C (krausCombination A c))
        ≤ ‖c‖ ^ 2 * (qform (choiOf A) (vec C)).re :=
      normSq_hsInner_krausCombination_le A c C
    _ = (qform (choiOf A) (vec C)).re := by rw [hc]; norm_num
    _ ≤ schmidtOperatorNorm (choiOf A) k * ‖vec C‖ ^ 2 :=
      re_qform_le_schmidtOperatorNorm_mul_norm_sq
        (choiOf A) k (vec C) (by simpa [pureSchmidtRank] using hrank)
    _ = schmidtOperatorNorm (choiOf A) k * hsNormSq C := by
      rw [hsNormSq_eq_norm_sq]

theorem krausActionValues_bddAbove
    (A : ι → Matrix W W ℂ) (k : ℕ) :
    BddAbove (krausActionValues A k) := by
  refine ⟨schmidtOperatorNorm (choiOf A) k, ?_⟩
  intro x hx
  rcases hx with hx | hx
  · rw [Set.mem_singleton_iff.mp hx]
    exact schmidtOperatorNorm_nonneg _ _
  · obtain ⟨c, hc, rfl⟩ := hx
    exact kyFanSq_krausCombination_le_schmidtOperatorNorm A k c hc

/-- The Kraus-action supremum is bounded by the Choi `S(k)` norm. -/
theorem krausActionNorm_le_schmidtOperatorNorm
    (A : ι → Matrix W W ℂ) (k : ℕ) :
    krausActionNorm A k ≤ schmidtOperatorNorm (choiOf A) k := by
  apply csSup_le (krausActionValues_nonempty A k)
  intro x hx
  rcases hx with hx | hx
  · rw [Set.mem_singleton_iff.mp hx]
    exact schmidtOperatorNorm_nonneg _ _
  · obtain ⟨c, hc, rfl⟩ := hx
    exact kyFanSq_krausCombination_le_schmidtOperatorNorm A k c hc

/-- A normalized rank-`k` test matrix is controlled by the Kraus-action
supremum. -/
theorem re_qform_choiOf_le_krausActionNorm
    (A : ι → Matrix W W ℂ) (k : ℕ)
    (C : Matrix W W ℂ) (hrank : C.rank ≤ k)
    (hC : hsNormSq C = 1) :
    (qform (choiOf A) (vec C)).re ≤ krausActionNorm A k := by
  let q : ℝ := (qform (choiOf A) (vec C)).re
  have hqsum :
      q = ∑ a, Complex.normSq (inner ℂ (vec (A a)) (vec C)) := by
    exact re_qform_choiOf A (vec C)
  have hq0 : 0 ≤ q := by
    rw [hqsum]
    exact Finset.sum_nonneg fun a _ => Complex.normSq_nonneg _
  by_cases hqz : q = 0
  · change q ≤ krausActionNorm A k
    rw [hqz]
    apply le_csSup (krausActionValues_bddAbove A k)
    exact Set.mem_union_left _ (Set.mem_singleton 0)
  · have hqpos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hqz)
    let s : ℝ := Real.sqrt q
    let c : EuclideanSpace ℂ ι :=
      WithLp.toLp 2 fun a =>
        ((s : ℂ)⁻¹ * inner ℂ (vec (A a)) (vec C))
    have hspos : 0 < s := Real.sqrt_pos.2 hqpos
    have hsSq : s ^ 2 = q := by
      dsimp only [s]
      exact Real.sq_sqrt hq0
    have hcnorm : ‖c‖ = 1 := by
      have hsq : ‖c‖ ^ 2 = 1 := by
        rw [EuclideanSpace.norm_sq_eq]
        dsimp only [c]
        simp_rw [← Complex.normSq_eq_norm_sq]
        simp_rw [Complex.normSq_mul, Complex.normSq_inv,
          Complex.normSq_ofReal]
        rw [← Finset.mul_sum, ← hqsum, ← hsSq]
        simpa [pow_two] using
          (inv_mul_cancel₀ (pow_ne_zero 2 (ne_of_gt hspos)))
      nlinarith [norm_nonneg c]
    have hpair :
        Complex.normSq (hsInner C (krausCombination A c)) = q := by
      have hinner :
          hsInner C (krausCombination A c) = (s : ℂ) := by
        rw [krausCombination, hsInner_sum_right]
        dsimp only [c]
        calc
          ∑ a,
              hsInner C
                (((s : ℂ)⁻¹ * inner ℂ (vec (A a)) (vec C)) • A a) =
              ∑ a,
                ((s : ℂ)⁻¹ * inner ℂ (vec (A a)) (vec C)) *
                  conj (inner ℂ (vec (A a)) (vec C)) := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [hsInner_smul_right]
            congr 1
            rw [hsInner_eq_inner, inner_conj_symm]
          _ = (s : ℂ)⁻¹ *
                ∑ a, (Complex.normSq
                  (inner ℂ (vec (A a)) (vec C)) : ℂ) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro a ha
            rw [mul_assoc, Complex.mul_conj]
          _ = (s : ℂ)⁻¹ * (q : ℂ) := by rw [hqsum]; norm_cast
          _ = (s : ℂ) := by
            rw [show (q : ℂ) = (s : ℂ) * (s : ℂ) by
              norm_cast; nlinarith [hsSq]]
            field_simp
      rw [hinner, Complex.normSq_ofReal]
      nlinarith [hsSq]
    have hky :
        q ≤ kyFanSq k (krausCombination A c) := by
      rw [← hpair]
      calc
        Complex.normSq (hsInner C (krausCombination A c))
            ≤ hsNormSq C * kyFanSq k (krausCombination A c) :=
          normSq_hsInner_le_hsNormSq_mul_kyFanSq
            C (krausCombination A c) hrank
        _ = kyFanSq k (krausCombination A c) := by rw [hC, one_mul]
    exact hky.trans
      (le_csSup (krausActionValues_bddAbove A k)
        (Set.mem_union_right _ ⟨c, hcnorm, rfl⟩))

/-- The `S(k)` norm of a Kraus Choi operator is at most its Kraus-action
supremum. -/
theorem schmidtOperatorNorm_choiOf_le_krausActionNorm
    (A : ι → Matrix W W ℂ) (k : ℕ) :
    schmidtOperatorNorm (choiOf A) k ≤ krausActionNorm A k := by
  apply csSup_le (schmidtOperatorValues_nonempty (choiOf A) k)
  intro x hx
  rcases hx with hx | hx
  · rw [Set.mem_singleton_iff.mp hx]
    apply le_csSup (krausActionValues_bddAbove A k)
    exact Set.mem_union_left _ (Set.mem_singleton 0)
  · obtain ⟨z, hz, hrank, rfl⟩ := hx
    simpa [hsNormSq_eq_norm_sq, hz] using
      re_qform_choiOf_le_krausActionNorm A k (unvec z)
        (by simpa [pureSchmidtRank] using hrank)
        (by rw [hsNormSq_eq_norm_sq, vec_unvec, hz]; norm_num)

/-- **Kraus-action formula.** The restricted Schmidt operator norm of a Choi
operator equals the supremal squared Ky Fan sum of normalized Kraus
combinations. -/
theorem schmidtOperatorNorm_choiOf_eq_krausActionNorm
    (A : ι → Matrix W W ℂ) (k : ℕ) :
    schmidtOperatorNorm (choiOf A) k = krausActionNorm A k :=
  le_antisymm
    (schmidtOperatorNorm_choiOf_le_krausActionNorm A k)
    (krausActionNorm_le_schmidtOperatorNorm A k)

/-- The paper's level-two action formula:
`2 β₂ = sup_{‖c‖=1} (s₁(K_c)² + s₂(K_c)²)`. -/
theorem two_mul_betaTwo_choiOf_eq_krausActionNorm
    (A : ι → Matrix W W ℂ) :
    2 * betaTwo (choiOf A) = krausActionNorm A 2 := by
  rw [betaTwo, schmidtOperatorNorm_choiOf_eq_krausActionNorm]
  ring

end KrausActionNorm

end RankR
