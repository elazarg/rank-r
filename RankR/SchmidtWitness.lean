/-
The double-antisymmetric Schmidt-number application.

`Qm` is the regrouped projection
`Π_-^(m) ⊗ Π_-^(n)` from the manuscript.  This file proves:

* an explicit rank-four pure-state decomposition of every positive scalar
  multiple of `Qm`;
* the rank-two witness `1/2 I - Qm` unconditionally;
* the rank-three witness `3/4 I - Qm`, and exact Schmidt number four;
* the two displayed witness expectations for any normalized scalar multiple
  of `Qm`.

The `k = 3` projection `S(k)` bound invoked from Johnston--Kribs in
`cor:exact-schmidt-number` follows here from the level-three double-skew action
bound by a projection-duality argument.
-/
import RankR.TraceSeparation
import RankR.ChoiSkew
import RankR.KyFanAction
import RankR.Sharp

namespace RankR

open Matrix Finset ComplexConjugate
open scoped Kronecker

/-! ## A rank-four pure-state decomposition of `Qm` -/

section SkewRank

variable {W : Type*} [DecidableEq W]

/-- The two-column factor carrying the range of an elementary skew matrix. -/
noncomputable def skewUnitLeft (a b : W) : Matrix W (Fin 2) ℂ :=
  Matrix.of fun p i => ![eBasis a p, -(eBasis b p)] i

/-- The two-row factor carrying the covectors of an elementary skew matrix. -/
noncomputable def skewUnitRight (a b : W) : Matrix (Fin 2) W ℂ :=
  Matrix.of fun i q => ![conj (eBasis b q), conj (eBasis a q)] i

/-- Every elementary skew matrix factors through a two-dimensional space,
including the degenerate case `a = b`. -/
theorem skewUnit_eq_mul (a b : W) :
    skewUnit a b = skewUnitLeft a b * skewUnitRight a b := by
  by_cases hab : a = b
  · subst b
    ext p q
    simp only [skewUnit, skewUnitLeft, skewUnitRight, Matrix.mul_apply,
      Matrix.single_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, eBasis_apply,
      apply_ite (starRingEnd ℂ), map_one, map_zero]
    by_cases hqa : q = a <;> by_cases hpa : p = a <;> simp [hqa, hpa]
  · ext p q
    simp only [skewUnit, skewUnitLeft, skewUnitRight, Matrix.mul_apply,
      Matrix.single_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, eBasis_apply,
      apply_ite (starRingEnd ℂ), map_one, map_zero]
    by_cases hpa : p = a <;> by_cases hqb : q = b <;> by_cases hpb : p = b <;>
      by_cases hqa : q = a <;> simp_all [eq_comm]

end SkewRank

section DoubleSkewDecomposition

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]

/-- Every elementary double-skew Kraus operator has matrix rank at most four.
The proof is the tensor product of the two explicit two-dimensional
factorizations above. -/
theorem rank_smul_skewKraus_le_four (c : ℂ) (f : KIdx U V) :
    (c • skewKraus f).rank ≤ 4 := by
  rw [skewKraus, skewUnit_eq_mul, skewUnit_eq_mul, Matrix.mul_kronecker_mul,
    ← Matrix.smul_mul]
  exact (Matrix.rank_mul_le_left _ _).trans (by
    simpa only [Fintype.card_prod, Fintype.card_fin, Nat.reduceMul] using
      Matrix.rank_le_card_width
        (c • (skewUnitLeft f.1.1 f.1.2 ⊗ₖ skewUnitLeft f.2.1 f.2.2)))

/-- The scaled redundant double-skew Kraus family whose pure projectors sum to
`Qm`. -/
noncomputable def scaledSkewKraus (t : ℝ) (f : KIdx U V) :
    Matrix (U × V) (U × V) ℂ :=
  ((Real.sqrt t / 4 : ℝ) : ℂ) • skewKraus f

/-- The redundant double-skew Kraus decomposition is an explicit pure-state
decomposition of `t Qm`. -/
theorem sum_rankOne_scaledSkewKraus (t : ℝ) (ht : 0 ≤ t) :
    (∑ f, rankOne (vec (scaledSkewKraus t f)) (vec (scaledSkewKraus t f))) =
      (t : ℂ) • (Qm : Matrix (Idx U V) (Idx U V) ℂ) := by
  have hsqrt : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht
  have hcoef :
      (((Real.sqrt t / 4 : ℝ) : ℂ) * ((Real.sqrt t / 4 : ℝ) : ℂ)) =
        ((t / 16 : ℝ) : ℂ) := by
    norm_cast
    calc
      Real.sqrt t / 4 * (Real.sqrt t / 4) =
          Real.sqrt t ^ 2 / 16 := by ring
      _ = t / 16 := by rw [hsqrt]
  calc
    (∑ f, rankOne (vec (scaledSkewKraus t f)) (vec (scaledSkewKraus t f))) =
        ((t / 16 : ℝ) : ℂ) • choiOf (skewKraus (U := U) (V := V)) := by
      ext X Y
      simp only [Matrix.sum_apply, scaledSkewKraus, vec_smul, rankOne,
        Matrix.of_apply, PiLp.smul_apply, smul_eq_mul, map_mul, choiOf,
        Matrix.smul_apply]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f _
      rw [Complex.conj_ofReal]
      calc
        ((Real.sqrt t / 4 : ℝ) : ℂ) * (vec (skewKraus f)).ofLp X
              * (((Real.sqrt t / 4 : ℝ) : ℂ)
                * (starRingEnd ℂ) ((vec (skewKraus f)).ofLp Y)) =
            (((Real.sqrt t / 4 : ℝ) : ℂ)
              * ((Real.sqrt t / 4 : ℝ) : ℂ))
                * ((vec (skewKraus f)).ofLp X
                  * (starRingEnd ℂ) ((vec (skewKraus f)).ofLp Y)) := by
            ring
        _ = ((t / 16 : ℝ) : ℂ)
              * ((vec (skewKraus f)).ofLp X
                * (starRingEnd ℂ) ((vec (skewKraus f)).ofLp Y)) := by
            rw [hcoef]
    _ = (t : ℂ) • Qm := by
      rw [choiOf_skewKraus]
      ext X Y
      simp only [Matrix.smul_apply, smul_eq_mul]
      push_cast
      ring

/-- Every nonnegative scalar multiple of the double-antisymmetric projection
has Schmidt number at most four.  This is the upper-bound decomposition in
`cor:exact-schmidt-number`, written without normalizing the trace. -/
theorem schmidtNumberLE_four_smul_Qm (t : ℝ) (ht : 0 ≤ t) :
    SchmidtNumberLE (W := U × V) 4
      ((t : ℂ) • (Qm : Matrix (Idx U V) (Idx U V) ℂ)) := by
  let e := Fintype.equivFin (KIdx U V)
  refine ⟨Fintype.card (KIdx U V),
    fun i => scaledSkewKraus t (e.symm i), ?_, ?_⟩
  · intro i
    exact rank_smul_skewKraus_le_four _ _
  · calc
      (t : ℂ) • (Qm : Matrix (Idx U V) (Idx U V) ℂ) =
          ∑ f, rankOne (vec (scaledSkewKraus t f))
            (vec (scaledSkewKraus t f)) :=
        (sum_rankOne_scaledSkewKraus t ht).symm
      _ = ∑ i, rankOne (vec (scaledSkewKraus t (e.symm i)))
            (vec (scaledSkewKraus t (e.symm i))) := by
        exact ((e.symm).sum_comp fun f =>
          rankOne (vec (scaledSkewKraus t f)) (vec (scaledSkewKraus t f))).symm

end DoubleSkewDecomposition

/-! ## Rank-two and rank-three projection bounds -/

section ProjectionBounds

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]

/-- The projection-duality statement that the double antisymmetrizer has
`S(3)`-norm at most `3/4`.  It is packaged as a proposition for reuse and
proved below as `QmRankThreeBound_holds`. -/
def QmRankThreeBound (U V : Type*) [Fintype U] [Fintype V]
    [DecidableEq U] [DecidableEq V] : Prop :=
  ∀ C : Matrix (U × V) (U × V) ℂ, C.rank ≤ 3 →
    (qform Qm (vec C)).re ≤ (3 / 4 : ℝ) * hsNormSq C

/-- The corresponding rank-two projection bound is unconditional. -/
theorem qform_Qm_rank_two_le (C : Matrix (U × V) (U × V) ℂ)
    (hrank : C.rank ≤ 2) :
    (qform Qm (vec C)).re ≤ (1 / 2 : ℝ) * hsNormSq C := by
  rw [← norm_mulVecE_Qm_sq, ← vec_dsProj, ← hsNormSq_eq_norm_sq]
  have h := hsNormSq_dsProj_le doubleSkewBoundQm_holds C hrank
  linarith

/-- Projection duality at exact matrix rank three.  Factor `Mᵀ` so that `M`
is a sum of three rank-one matrices with orthonormal right factors.  The
level-three double-skew action bound controls the projection on those factors;
two Cauchy--Schwarz inequalities and cancellation give the factor `3/4`. -/
theorem hsNormSq_dsProj_le_three_of_rank_eq
    (M : Matrix (U × V) (U × V) ℂ) (hrank : M.rank = 3) :
    hsNormSq (dsProj M) ≤ (3 / 4 : ℝ) * hsNormSq M := by
  have hA0 : 0 ≤ hsNormSq (dsProj M) := hsNormSq_nonneg _
  have hB0 : 0 ≤ hsNormSq M := hsNormSq_nonneg M
  have hvK : vec (dsProj M) = mulVecE Qm (vec M) := vec_dsProj M
  have hfix : mulVecE Qm (vec (dsProj M)) = vec (dsProj M) := by
    rw [hvK, mulVecE_mul, Qm_mul_self]
  have hb : ((hsNormSq (dsProj M) : ℝ) : ℂ) = hsInner (dsProj M) M := by
    rw [← hsInner_self, hsInner_eq_inner, hsInner_eq_inner]
    nth_rewrite 2 [hvK]
    rw [inner_mulVecE_left, Qm_conjTranspose, hfix]
  obtain ⟨n, hn, e, d, he, hMeq, hdM⟩ :
      ∃ n : ℕ, n = 3 ∧ ∃ e d : Fin n → EuclideanSpace ℂ (U × V),
        Orthonormal ℂ e ∧ M = ∑ i, rankOne (d i) (e i) ∧
          ∑ i, ‖d i‖ ^ 2 = hsNormSq M := by
    obtain ⟨n, e₀, d₀, he₀, hMT, hn⟩ :
        ∃ n : ℕ, ∃ e d : Fin n → EuclideanSpace ℂ (U × V),
          Orthonormal ℂ e ∧ Mᵀ = rankFactor e d ∧ n = 3 := by
      obtain ⟨e₀, d₀, he₀, hMT⟩ := exists_rankFactor_rank Mᵀ
      exact ⟨Mᵀ.rank, e₀, d₀, he₀, hMT,
        by simpa only [Matrix.rank_transpose] using hrank⟩
    refine ⟨n, hn, fun i => bar (e₀ i), fun i => bar (d₀ i),
      orthonormal_conj he₀, ?_, ?_⟩
    · have h : (Mᵀ)ᵀ = (rankFactor e₀ d₀)ᵀ := congrArg (·ᵀ) hMT
      rw [Matrix.transpose_transpose, rankFactor_eq_sum, Matrix.transpose_sum] at h
      exact h.trans (Finset.sum_congr rfl fun i _ => transpose_rankOne _ _)
    · rw [← hsNormSq_transpose M, hMT, hsNormSq_rankFactor_eq e₀ d₀ he₀]
      exact Finset.sum_congr rfl fun i _ => by rw [norm_bar]
  have hterm : ∀ i, ‖hsInner (dsProj M) (rankOne (d i) (e i))‖
      ≤ ‖d i‖ * ‖mulVecE (dsProj M) (e i)‖ := fun i => by
    rw [hsInner_rankOne_right, RCLike.norm_conj]
    exact norm_inner_le_norm _ _
  have hsum : hsNormSq (dsProj M)
      ≤ ∑ i, ‖d i‖ * ‖mulVecE (dsProj M) (e i)‖ := by
    have h0 : ((hsNormSq (dsProj M) : ℝ) : ℂ)
        = ∑ i, hsInner (dsProj M) (rankOne (d i) (e i)) := by
      rw [hb, ← hsInner_sum_right, ← hMeq]
    calc
      hsNormSq (dsProj M) =
          ‖((hsNormSq (dsProj M) : ℝ) : ℂ)‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA0]
      _ = ‖∑ i, hsInner (dsProj M) (rankOne (d i) (e i))‖ := by rw [h0]
      _ ≤ ∑ i, ‖hsInner (dsProj M) (rankOne (d i) (e i))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i, ‖d i‖ * ‖mulVecE (dsProj M) (e i)‖ :=
        Finset.sum_le_sum fun i _ => hterm i
  have hcs : ∑ i, ‖d i‖ * ‖mulVecE (dsProj M) (e i)‖
      ≤ Real.sqrt (∑ i, ‖d i‖ ^ 2)
        * Real.sqrt (∑ i, ‖mulVecE (dsProj M) (e i)‖ ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  rw [hdM] at hcs
  have hS :
      ∑ i, ‖mulVecE (dsProj M) (e i)‖ ^ 2
        ≤ (3 / 4 : ℝ) * hsNormSq (dsProj M) := by
    simpa [hn] using sum_norm_sq_le_of_doubleSkewQm
      doubleSkewBoundQm_holds hfix (by omega) e he
  have hSnn : (0 : ℝ) ≤ ∑ i, ‖mulVecE (dsProj M) (e i)‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hAsq : hsNormSq (dsProj M) ^ 2
      ≤ hsNormSq M * ∑ i, ‖mulVecE (dsProj M) (e i)‖ ^ 2 := by
    have h2 := mul_self_le_mul_self hA0 (hsum.trans hcs)
    rw [← Real.sq_sqrt hB0, ← Real.sq_sqrt hSnn]
    nlinarith [h2]
  have hBS :
      hsNormSq M * (∑ i, ‖mulVecE (dsProj M) (e i)‖ ^ 2)
        ≤ hsNormSq M * ((3 / 4 : ℝ) * hsNormSq (dsProj M)) :=
    mul_le_mul_of_nonneg_left hS hB0
  nlinarith [hAsq, hBS, hA0, hB0]

/-- The double antisymmetrizer has `S(3)`-norm at most `3/4`. -/
theorem qform_Qm_rank_three_le (C : Matrix (U × V) (U × V) ℂ)
    (hrank : C.rank ≤ 3) :
    (qform Qm (vec C)).re ≤ (3 / 4 : ℝ) * hsNormSq C := by
  by_cases htwo : C.rank ≤ 2
  · have h := qform_Qm_rank_two_le C htwo
    have hC0 := hsNormSq_nonneg C
    nlinarith
  · have hthree : C.rank = 3 := by omega
    rw [← norm_mulVecE_Qm_sq, ← vec_dsProj, ← hsNormSq_eq_norm_sq]
    exact hsNormSq_dsProj_le_three_of_rank_eq C hthree

/-- The rank-three projection-duality interface is discharged
unconditionally. -/
theorem QmRankThreeBound_holds : QmRankThreeBound U V :=
  qform_Qm_rank_three_le

/-- The Schmidt-number witness `α I - Qm`. -/
noncomputable def schmidtWitness (α : ℝ) :
    Matrix (Idx U V) (Idx U V) ℂ :=
  (α : ℂ) • 1 - Qm

omit [Fintype U] [Fintype V] in
theorem schmidtWitness_isHermitian (α : ℝ) :
    (schmidtWitness (U := U) (V := V) α).IsHermitian := by
  rw [Matrix.IsHermitian, schmidtWitness, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Qm_conjTranspose]
  simp only [RCLike.star_def, Complex.conj_ofReal, Complex.coe_smul]

/-- A homogeneous pure-state bound makes `α I - Qm` block positive. -/
theorem schmidtWitness_isBlockPositive {r : ℕ} {α : ℝ}
    (h : ∀ C : Matrix (U × V) (U × V) ℂ, C.rank ≤ r →
      (qform Qm (vec C)).re ≤ α * hsNormSq C) :
    IsBlockPositive r (schmidtWitness (U := U) (V := V) α) := by
  intro C hrank
  have hQ := h C hrank
  rw [schmidtWitness, qform_sub, qform_smul, qform_one, Complex.sub_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    ← hsNormSq_eq_norm_sq]
  simp only [Complex.ofReal_re]
  linarith

/-- `W₂ = 1/2 I - Qm` is a Schmidt-number-two witness. -/
theorem twoWitness_isBlockPositive :
    IsBlockPositive 2 (schmidtWitness (U := U) (V := V) (1 / 2)) :=
  schmidtWitness_isBlockPositive qform_Qm_rank_two_le

/-- `W₃ = 3/4 I - Qm` is a Schmidt-number-three witness. -/
theorem threeWitness_isBlockPositive :
    IsBlockPositive 3 (schmidtWitness (U := U) (V := V) (3 / 4)) :=
  schmidtWitness_isBlockPositive qform_Qm_rank_three_le

/-- The two displayed witness inequalities on mixed states. -/
theorem trace_mul_twoWitness_nonneg {ρ : Matrix (Idx U V) (Idx U V) ℂ}
    (hρ : SchmidtNumberLE (W := U × V) 2 ρ) :
    0 ≤ ((schmidtWitness (U := U) (V := V) (1 / 2) * ρ).trace).re :=
  trace_mul_nonneg_of_schmidtNumberLE
    (schmidtWitness_isHermitian (U := U) (V := V) (1 / 2))
    twoWitness_isBlockPositive hρ

theorem trace_mul_threeWitness_nonneg {ρ : Matrix (Idx U V) (Idx U V) ℂ}
    (hρ : SchmidtNumberLE (W := U × V) 3 ρ) :
    0 ≤ ((schmidtWitness (U := U) (V := V) (3 / 4) * ρ).trace).re :=
  trace_mul_nonneg_of_schmidtNumberLE
    (schmidtWitness_isHermitian (U := U) (V := V) (3 / 4))
    threeWitness_isBlockPositive hρ

end ProjectionBounds

/-! ## Exact lower bound and witness expectations -/

section ExactSchmidtNumber

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]

/-- Idempotence and self-adjointness identify the trace and squared
Hilbert--Schmidt norm of `Qm`. -/
theorem trace_Qm_eq_hsNormSq :
    (Qm : Matrix (Idx U V) (Idx U V) ℂ).trace =
      (hsNormSq (Qm : Matrix (Idx U V) (Idx U V) ℂ) : ℂ) := by
  calc
    (Qm : Matrix (Idx U V) (Idx U V) ℂ).trace =
        ((Qm : Matrix (Idx U V) (Idx U V) ℂ) * Qm).trace :=
      congrArg Matrix.trace Qm_mul_self.symm
    _ = hsInner (Qm : Matrix (Idx U V) (Idx U V) ℂ) Qm := by
      rw [hsInner, Qm_conjTranspose]
    _ = (hsNormSq (Qm : Matrix (Idx U V) (Idx U V) ℂ) : ℂ) :=
      hsInner_self _

/-- Pairing a witness with the projection itself gives
`(α - 1) ‖Qm‖₂²`. -/
theorem re_hsInner_schmidtWitness_Qm (α : ℝ) :
    (hsInner (schmidtWitness (U := U) (V := V) α)
      (Qm : Matrix (Idx U V) (Idx U V) ℂ)).re =
        (α - 1) * hsNormSq (Qm : Matrix (Idx U V) (Idx U V) ℂ) := by
  rw [schmidtWitness, hsInner_sub_left, hsInner_smul_left,
    show hsInner (1 : Matrix (Idx U V) (Idx U V) ℂ) Qm = Qm.trace by
      simp only [hsInner, Matrix.conjTranspose_one, Matrix.one_mul]
      rfl,
    hsInner_self, trace_Qm_eq_hsNormSq]
  simp only [Complex.conj_ofReal, Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

/-- Distinct labels in both local factors make `Qm` nonzero. -/
theorem Qm_ne_zero {a₀ a₁ : U} {b₀ b₁ : V}
    (ha : a₀ ≠ a₁) (hb : b₀ ≠ b₁) :
    (Qm : Matrix (Idx U V) (Idx U V) ℂ) ≠ 0 := by
  intro hQ
  have h := qform_Qm_sharpWit ha hb
  rw [hQ] at h
  simp [qform] at h

/-- A positive scalar multiple of `Qm` is not in the
Schmidt-number-three cone. -/
theorem not_schmidtNumberLE_three_smul_Qm
    {a₀ a₁ : U} {b₀ b₁ : V} (ha : a₀ ≠ a₁) (hb : b₀ ≠ b₁)
    (t : ℝ) (ht : 0 < t) :
    ¬ SchmidtNumberLE (W := U × V) 3
      ((t : ℂ) • (Qm : Matrix (Idx U V) (Idx U V) ℂ)) := by
  intro hSN
  have hnonneg := re_hsInner_nonneg_of_schmidtNumberLE
    threeWitness_isBlockPositive hSN
  rw [hsInner_smul_right, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, re_hsInner_schmidtWitness_Qm] at hnonneg
  have hQpos :
      0 < hsNormSq (Qm : Matrix (Idx U V) (Idx U V) ℂ) :=
    hsNormSq_pos (Qm_ne_zero ha hb)
  norm_num at hnonneg
  nlinarith

/-- Exact Schmidt number four for every positive scalar multiple of `Qm`. -/
theorem doubleAntisym_schmidt_number_eq_four
    {a₀ a₁ : U} {b₀ b₁ : V} (ha : a₀ ≠ a₁) (hb : b₀ ≠ b₁)
    (t : ℝ) (ht : 0 < t) :
    SchmidtNumberLE (W := U × V) 4
        ((t : ℂ) • (Qm : Matrix (Idx U V) (Idx U V) ℂ))
      ∧ ¬ SchmidtNumberLE (W := U × V) 3
        ((t : ℂ) • (Qm : Matrix (Idx U V) (Idx U V) ℂ)) := by
  exact ⟨schmidtNumberLE_four_smul_Qm t ht.le,
    not_schmidtNumberLE_three_smul_Qm ha hb t ht⟩

/-- A normalized scalar multiple of `Qm` is fixed by left multiplication by
`Qm`. -/
theorem Qm_mul_smul_Qm (t : ℝ) :
    (Qm : Matrix (Idx U V) (Idx U V) ℂ) * ((t : ℂ) • Qm) =
      (t : ℂ) • Qm := by
  rw [Matrix.mul_smul, Qm_mul_self]

/-- A witness has expectation `α - 1` on any trace-one state supported on the
range of `Qm`. -/
theorem trace_mul_schmidtWitness_eq_sub_one (α : ℝ)
    (ρ : Matrix (Idx U V) (Idx U V) ℂ) (htrace : ρ.trace = 1)
    (hsupport : (Qm : Matrix (Idx U V) (Idx U V) ℂ) * ρ = ρ) :
    ((schmidtWitness (U := U) (V := V) α * ρ).trace).re = α - 1 := by
  rw [schmidtWitness, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul,
    hsupport, Matrix.trace_sub, Matrix.trace_smul, htrace]
  simp

/-- The two exact expectations in `cor:explicit-witnesses`.  The hypothesis is
only the normalization of the scalar multiple; support follows from
idempotence of `Qm`. -/
theorem trace_mul_twoWitness_smul_Qm (t : ℝ)
    (htrace : (((t : ℂ) • (Qm : Matrix (Idx U V) (Idx U V) ℂ)).trace) = 1) :
    ((schmidtWitness (U := U) (V := V) (1 / 2)
      * ((t : ℂ) • Qm)).trace).re = -(1 / 2 : ℝ) := by
  rw [trace_mul_schmidtWitness_eq_sub_one _ _ htrace (Qm_mul_smul_Qm t)]
  norm_num

theorem trace_mul_threeWitness_smul_Qm (t : ℝ)
    (htrace : (((t : ℂ) • (Qm : Matrix (Idx U V) (Idx U V) ℂ)).trace) = 1) :
    ((schmidtWitness (U := U) (V := V) (3 / 4)
      * ((t : ℂ) • Qm)).trace).re = -(1 / 4 : ℝ) := by
  rw [trace_mul_schmidtWitness_eq_sub_one _ _ htrace (Qm_mul_smul_Qm t)]
  norm_num

end ExactSchmidtNumber

end RankR
