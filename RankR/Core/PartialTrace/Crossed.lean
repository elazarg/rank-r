/-
The local input to the balanced-factorization proof of the partial-trace
inequality.

The two partial traces are packaged as one map into a Hilbert direct sum.  Its
four-linear crossing symmetry and sharp rank-one estimate follow from the
four-state marginal identities and the double-antisymmetric projection
certificate.
-/
import RankR.Core.Amplification.Balanced
import RankR.Core.DoubleSkew.Flip

namespace RankR

open Matrix Finset ComplexConjugate

section PartialTracePair

variable {U V : Type*} [Fintype U] [Fintype V]

/-- The two partial traces, regarded as one map into their Hilbert direct sum. -/
noncomputable def partialTracePair :
    Matrix (U × V) (U × V) ℂ →ₗ[ℂ]
      EuclideanSpace ℂ ((V × V) ⊕ (U × U)) where
  toFun C := matrixSumVec (ptraceU C) (ptraceV C)
  map_add' C D := by
    ext p
    cases p with
    | inl p =>
        change ptraceU (C + D) p.1 p.2 =
          ptraceU C p.1 p.2 + ptraceU D p.1 p.2
        simp only [ptraceU_apply, Matrix.add_apply, Finset.sum_add_distrib]
    | inr p =>
        change ptraceV (C + D) p.1 p.2 =
          ptraceV C p.1 p.2 + ptraceV D p.1 p.2
        simp only [ptraceV_apply, Matrix.add_apply, Finset.sum_add_distrib]
  map_smul' c C := by
    ext p
    cases p with
    | inl p =>
        change ptraceU (c • C) p.1 p.2 = c • ptraceU C p.1 p.2
        simp only [ptraceU_apply, Matrix.smul_apply, smul_eq_mul,
          Finset.mul_sum]
    | inr p =>
        change ptraceV (c • C) p.1 p.2 = c • ptraceV C p.1 p.2
        simp only [ptraceV_apply, Matrix.smul_apply, smul_eq_mul,
          Finset.mul_sum]

@[simp]
theorem partialTracePair_apply (C : Matrix (U × V) (U × V) ℂ) :
    partialTracePair C = matrixSumVec (ptraceU C) (ptraceV C) :=
  rfl

/-- The norm of the paired map is the sum of the two marginal squared norms. -/
theorem norm_partialTracePair_sq (C : Matrix (U × V) (U × V) ℂ) :
    ‖partialTracePair C‖ ^ 2 =
      hsNormSq (ptraceU C) + hsNormSq (ptraceV C) :=
  normSq_matrixSumVec _ _

/-- The paired-map inner product is the sum of the two marginal pairings. -/
theorem inner_partialTracePair (C D : Matrix (U × V) (U × V) ℂ) :
    inner ℂ (partialTracePair C) (partialTracePair D) =
      hsInner (ptraceU C) (ptraceU D) + hsInner (ptraceV C) (ptraceV D) :=
  inner_matrixSumVec _ _ _ _

end PartialTracePair

section Crossing

variable {U V : Type*} [Fintype U] [Fintype V]

/-- Simultaneously reverse the two pairs of indices in a four-fold sum. -/
private theorem sum4_reverse_pairs
    {A B M : Type*} [Fintype A] [Fintype B] [AddCommMonoid M]
    (F : A → A → B → B → M) :
    (∑ a, ∑ a', ∑ b, ∑ b', F a a' b b')
      = ∑ a, ∑ a', ∑ b, ∑ b', F a' a b' b := by
  calc
    _ = ∑ a', ∑ a, ∑ b, ∑ b', F a a' b b' := Finset.sum_comm
    _ = ∑ a', ∑ a, ∑ b', ∑ b, F a a' b b' := by
      refine Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := rfl

/-- Crossing a rank-one pairing exchanges the `U` marginal with the `V`
marginal. -/
theorem hsInner_ptraceU_rankOne_cross
    (u v s t : EuclideanSpace ℂ (U × V)) :
    hsInner (ptraceU (rankOne u v)) (ptraceU (rankOne s t))
      = hsInner (ptraceV (rankOne t v)) (ptraceV (rankOne s u)) := by
  rw [hsInner_ptraceU_rankOne, hsInner_ptraceV_rankOne]
  simp_rw [Finset.sum_mul_sum]
  conv_rhs => rw [sum4_swap]
  calc
    _ = ∑ a, ∑ a', ∑ b, ∑ c,
        conj (u (a', c)) * s (a, c) * (v (a', b) * conj (t (a, b))) :=
      sum4_reverse_pairs _
    _ = _ := by
      refine Finset.sum_congr rfl fun a _ =>
        Finset.sum_congr rfl fun a' _ =>
          Finset.sum_congr rfl fun b _ =>
            Finset.sum_congr rfl fun c _ => ?_
      ring

/-- The mirror crossing identity. -/
theorem hsInner_ptraceV_rankOne_cross
    (u v s t : EuclideanSpace ℂ (U × V)) :
    hsInner (ptraceV (rankOne u v)) (ptraceV (rankOne s t))
      = hsInner (ptraceU (rankOne t v)) (ptraceU (rankOne s u)) := by
  rw [hsInner_ptraceV_rankOne, hsInner_ptraceU_rankOne]
  simp_rw [Finset.sum_mul_sum]
  conv_rhs => rw [sum4_swap]
  calc
    _ = ∑ b, ∑ b', ∑ a, ∑ a',
        conj (u (a', b')) * s (a', b) * (v (a, b') * conj (t (a, b))) :=
      sum4_reverse_pairs _
    _ = _ := by
      refine Finset.sum_congr rfl fun b _ =>
        Finset.sum_congr rfl fun b' _ =>
          Finset.sum_congr rfl fun a _ =>
            Finset.sum_congr rfl fun a' _ => ?_
      ring

/-- The partial-trace pair has the four-linear crossing symmetry used by the
balanced-polarization lift. -/
theorem partialTracePair_hasCrossedPolarization :
    HasCrossedPolarization (partialTracePair (U := U) (V := V)) := by
  intro u v s t
  rw [inner_partialTracePair, inner_partialTracePair]
  calc
    hsInner (ptraceU (rankOne u v)) (ptraceU (rankOne s t))
          + hsInner (ptraceV (rankOne u v)) (ptraceV (rankOne s t))
        = hsInner (ptraceV (rankOne t v)) (ptraceV (rankOne s u))
          + hsInner (ptraceU (rankOne t v)) (ptraceU (rankOne s u)) :=
      congrArg₂ (· + ·)
        (hsInner_ptraceU_rankOne_cross u v s t)
        (hsInner_ptraceV_rankOne_cross u v s t)
    _ = _ := add_comm _ _

end Crossing

section RankOne

variable {U V : Type*} [Fintype U] [Fintype V]

/-- The unstarred tensor outer product used to expose the two local flip
operators in the rank-one defect. -/
private def tensorOuter
    (x y : EuclideanSpace ℂ (U × V)) :
    Matrix (U × V) (U × V) ℂ :=
  fun p q => x p * y q

omit [Fintype U] [Fintype V] in
@[simp]
private theorem tensorOuter_apply
    (x y : EuclideanSpace ℂ (U × V)) (p q : U × V) :
    tensorOuter x y p q = x p * y q :=
  rfl

/-- Swap the two middle binders in a four-fold sum. -/
private theorem sum4_swap_middle
    {A B C D M : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [AddCommMonoid M] (F : A → B → C → D → M) :
    (∑ a, ∑ b, ∑ c, ∑ d, F a b c d)
      = ∑ a, ∑ c, ∑ b, ∑ d, F a b c d := by
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- The unstarred tensor outer product has product Hilbert--Schmidt norm. -/
private theorem hsNormSq_tensorOuter
    (x y : EuclideanSpace ℂ (U × V)) :
    hsNormSq (tensorOuter x y) = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  rw [hsNormSq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp only [tensorOuter_apply, Complex.normSq_eq_norm_sq, norm_mul, mul_pow]
  rw [Finset.sum_mul_sum]

/-- A `U` flip of the tensor outer product is the `U`-marginal norm of the
corresponding rank-one operator. -/
private theorem hsInner_tensorOuter_flipU
    (x y : EuclideanSpace ℂ (U × V)) :
    hsInner (tensorOuter x y) (flipU (tensorOuter x y))
      = (hsNormSq (ptraceU (rankOne x y)) : ℂ) := by
  rw [← hsInner_self, hsInner_ptraceU_rankOne, hsInner_eq_sum_vec]
  simp only [Fintype.sum_prod_type, vec_apply, tensorOuter_apply, flipU_apply,
    map_mul]
  simp_rw [Finset.sum_mul_sum]
  rw [sum4_swap_middle]
  refine Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun a' _ =>
      Finset.sum_congr rfl fun b _ =>
        Finset.sum_congr rfl fun c _ => ?_
  ring

/-- The mirror identity for the `V` flip. -/
private theorem hsInner_tensorOuter_flipV
    (x y : EuclideanSpace ℂ (U × V)) :
    hsInner (tensorOuter x y) (flipV (tensorOuter x y))
      = (hsNormSq (ptraceV (rankOne x y)) : ℂ) := by
  rw [← hsInner_self, hsInner_ptraceV_rankOne, hsInner_eq_sum_vec]
  simp only [Fintype.sum_prod_type, vec_apply, tensorOuter_apply, flipV_apply,
    map_mul]
  simp_rw [Finset.sum_mul_sum]
  rw [sum4_swap_middle, sum4_swap]
  refine Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun b' _ =>
      Finset.sum_congr rfl fun a _ =>
        Finset.sum_congr rfl fun a' _ => ?_
  ring

/-- Simultaneously flipping both local factors yields the scalar overlap. -/
private theorem hsInner_tensorOuter_transpose
    (x y : EuclideanSpace ℂ (U × V)) :
    hsInner (tensorOuter x y) (tensorOuter x y)ᵀ
      = (Complex.normSq (inner ℂ y x) : ℂ) := by
  rw [hsInner_eq_sum_vec, Complex.normSq_eq_conj_mul_self,
    PiLp.inner_apply]
  simp only [vec_apply, tensorOuter_apply, Matrix.transpose_apply,
    RCLike.inner_apply', map_sum, map_mul, Complex.conj_conj]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun p _ =>
    Finset.sum_congr rfl fun q _ => by ring

/-- The sharp rank-one defect is four times the squared norm of the
double-antisymmetric component of the unstarred tensor outer product. -/
private theorem rankOne_partialTrace_defect_eq
    [DecidableEq U] [DecidableEq V]
    (x y : EuclideanSpace ℂ (U × V)) :
    ‖x‖ ^ 2 * ‖y‖ ^ 2 + Complex.normSq (inner ℂ y x)
        - hsNormSq (ptraceU (rankOne x y))
        - hsNormSq (ptraceV (rankOne x y))
      = 4 * ‖mulVecE (Qm (U := U) (V := V)) (vec (tensorOuter x y))‖ ^ 2 := by
  classical
  rw [norm_mulVecE_Qm_sq, qform_Qm_vec, hsInner_self,
    hsNormSq_tensorOuter, hsInner_tensorOuter_flipU,
    hsInner_tensorOuter_flipV, hsInner_tensorOuter_transpose]
  norm_num [pow_two, Complex.mul_re]
  ring

/-- The sharp rank-one inequality for the two partial traces. -/
theorem hsNormSq_partialTrace_rankOne_add_le
    (x y : EuclideanSpace ℂ (U × V)) :
    hsNormSq (ptraceU (rankOne x y)) + hsNormSq (ptraceV (rankOne x y))
      ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 + Complex.normSq (inner ℂ y x) := by
  classical
  have h := rankOne_partialTrace_defect_eq x y
  have hnonneg :
      0 ≤ 4 * ‖mulVecE (Qm (U := U) (V := V))
        (vec (tensorOuter x y))‖ ^ 2 := by positivity
  linarith

/-- The paired partial-trace map satisfies the rank-one hypothesis of the
balanced-polarization lift. -/
theorem partialTracePair_hasRankOneTraceBound :
    HasRankOneTraceBound (partialTracePair (U := U) (V := V)) := by
  intro x y
  rw [norm_partialTracePair_sq]
  exact hsNormSq_partialTrace_rankOne_add_le x y

/-- The level-one constant for the double antisymmetrizer, where `m` is the
smaller local dimension. -/
noncomputable def doubleSkewRankOneConstant (m : ℕ) : ℝ := ((m : ℝ) - 1) / (2 * m)

private theorem card_mul_hsNormSq_ge_trace {W : Type*} [Fintype W]
    (A : Matrix W W ℂ) :
    Complex.normSq A.trace ≤ (Fintype.card W : ℝ) * hsNormSq A :=
  (normSq_trace_le_rank A).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast Matrix.rank_le_card_width A)
      (hsNormSq_nonneg A))

private theorem inner_self_complex (x : EuclideanSpace ℂ (U × V)) :
    inner ℂ x x = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  calc
    inner ℂ x x = ((‖x‖ : ℂ) ^ 2) := inner_self_eq_norm_sq_to_K x
    _ = _ := (Complex.ofReal_pow ‖x‖ 2).symm

private theorem trace_ptraces_rankOne_self (x : EuclideanSpace ℂ (U × V)) :
    (ptraceU (rankOne x x)).trace = (‖x‖ ^ 2 : ℝ) ∧
      (ptraceV (rankOne x x)).trace = (‖x‖ ^ 2 : ℝ) := by
  have h := trace_rankOne x x
  rw [inner_self_complex] at h
  constructor
  · rw [← h]
    simp only [Matrix.trace, Matrix.diag_apply, ptraceU_apply, Fintype.sum_prod_type]
    exact Finset.sum_comm
  · rw [← h]
    simp only [Matrix.trace, Matrix.diag_apply, ptraceV_apply, Fintype.sum_prod_type]

omit [Fintype U] [Fintype V] in
private theorem tensorOuter_self_transpose (x : EuclideanSpace ℂ (U × V)) :
    (tensorOuter x x)ᵀ = tensorOuter x x := by
  ext p q
  exact mul_comm _ _

private theorem hsNormSq_ptraces_rankOne_self (x : EuclideanSpace ℂ (U × V)) :
    hsNormSq (ptraceU (rankOne x x)) = hsNormSq (ptraceV (rankOne x x)) := by
  have h := flipV_eq_flipU (tensorOuter_self_transpose x)
  have he := congrArg (hsInner (tensorOuter x x)) h
  rw [hsInner_tensorOuter_flipV, hsInner_tensorOuter_flipU] at he
  exact Complex.ofReal_injective he.symm

private theorem norm_Qm_tensorOuter_self_sq_le
    [DecidableEq U] [DecidableEq V] [Nonempty U] [Nonempty V]
    (x : EuclideanSpace ℂ (U × V)) :
    ‖mulVecE Qm (vec (tensorOuter x x))‖ ^ 2 ≤
      doubleSkewRankOneConstant (min (Fintype.card U) (Fintype.card V)) * (‖x‖ ^ 2) ^ 2 := by
  obtain ⟨hu, hv⟩ := trace_ptraces_rankOne_self x
  have hU := card_mul_hsNormSq_ge_trace (ptraceU (rankOne x x))
  have hV := card_mul_hsNormSq_ge_trace (ptraceV (rankOne x x))
  rw [hu, Complex.normSq_ofReal] at hU
  rw [hv, Complex.normSq_ofReal, ← hsNormSq_ptraces_rankOne_self x] at hV
  have hmin : (‖x‖ ^ 2) ^ 2 ≤ ((min (Fintype.card U) (Fintype.card V) : ℕ) : ℝ) *
      hsNormSq (ptraceU (rankOne x x)) := by
    by_cases h : Fintype.card U ≤ Fintype.card V
    · simpa only [min_eq_left h, pow_two] using hV
    · simpa only [min_eq_right (Nat.le_of_not_ge h), pow_two] using hU
  have hm : (0 : ℝ) < (min (Fintype.card U) (Fintype.card V) : ℕ) := by
    exact_mod_cast lt_min Fintype.card_pos Fintype.card_pos
  have h := rankOne_partialTrace_defect_eq x x
  rw [inner_self_complex, Complex.normSq_ofReal, ← hsNormSq_ptraces_rankOne_self x] at h
  rw [doubleSkewRankOneConstant, div_mul_eq_mul_div, le_div_iff₀ (show 0 < 2 * ((min (Fintype.card U) (Fintype.card V) : ℕ) : ℝ) by positivity)]
  have he := congrArg (fun a : ℝ => ((min (Fintype.card U) (Fintype.card V) : ℕ) : ℝ) * a) h
  nlinarith only [he, hmin]

omit [Fintype U] [Fintype V] in
private theorem tensorOuter_eq_rankOne_bar (x y : EuclideanSpace ℂ (U × V)) :
    tensorOuter x y = rankOne x (bar y) := by
  ext p q
  simp [tensorOuter_apply, rankOne]

omit [Fintype U] [Fintype V] in
private theorem tensorOuter_smul_smul (a b : ℂ) (x y : EuclideanSpace ℂ (U × V)) :
    tensorOuter (a • x) (b • y) = (a * b) • tensorOuter x y := by
  ext p q
  simp only [tensorOuter_apply, PiLp.smul_apply, smul_eq_mul, Matrix.smul_apply]
  ring

private theorem norm_Qm_tensorOuter_unit_le
    [DecidableEq U] [DecidableEq V] [Nonempty U] [Nonempty V]
    (x y : EuclideanSpace ℂ (U × V)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ‖mulVecE Qm (vec (tensorOuter x y))‖ ^ 2 ≤
      doubleSkewRankOneConstant (min (Fintype.card U) (Fintype.card V)) := by
  let c := doubleSkewRankOneConstant (min (Fintype.card U) (Fintype.card V))
  have hc : 0 ≤ c := by
    have h : 1 ≤ min (Fintype.card U) (Fintype.card V) :=
      le_min (Nat.succ_le_of_lt Fintype.card_pos) (Nat.succ_le_of_lt Fintype.card_pos)
    exact div_nonneg (sub_nonneg.mpr (by exact_mod_cast h)) (by positivity)
  let P (a b : EuclideanSpace ℂ (U × V)) := mulVecE Qm (vec (tensorOuter a b))
  have hdiag (a : EuclideanSpace ℂ (U × V)) : ‖P a a‖ ≤ Real.sqrt c * ‖a‖ ^ 2 := by
    apply le_of_pow_le_pow_left₀ (n := 2) (by decide) (by positivity)
    rw [mul_pow, Real.sq_sqrt hc]
    exact norm_Qm_tensorOuter_self_sq_le a
  have hpolar : P x y = (4 : ℂ)⁻¹ • (P (x + y) (x + y) - P (x - y) (x - y)) := by
    ext p
    simp only [P, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, mulVecE_Qm,
      vec_apply, tensorOuter_apply, PiLp.add_apply, swU, swV]
    ring
  have hpar := parallelogram_law_with_norm ℂ x y
  rw [hx, hy] at hpar
  have hnorm : ‖P x y‖ ≤ Real.sqrt c := by
    calc
      ‖P x y‖ = (1 / 4 : ℝ) * ‖P (x + y) (x + y) - P (x - y) (x - y)‖ := by
        rw [hpolar, norm_smul, norm_inv]
        norm_num
      _ ≤ (1 / 4 : ℝ) * (‖P (x + y) (x + y)‖ + ‖P (x - y) (x - y)‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)
      _ ≤ (1 / 4 : ℝ) * (Real.sqrt c * ‖x + y‖ ^ 2 + Real.sqrt c * ‖x - y‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add (hdiag _) (hdiag _)) (by norm_num)
      _ = Real.sqrt c := by nlinarith only [congrArg (fun a : ℝ => Real.sqrt c * a) hpar]
  change ‖P x y‖ ^ 2 ≤ c
  rw [← Real.sq_sqrt hc]
  exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2

/-- The sharp rank-one upper bound for the double antisymmetrizer. -/
theorem qform_Qm_rankOne_le
    [DecidableEq U] [DecidableEq V] [Nonempty U] [Nonempty V]
    (x y : EuclideanSpace ℂ (U × V)) :
    (qform Qm (vec (rankOne x y))).re ≤
      doubleSkewRankOneConstant (min (Fintype.card U) (Fintype.card V)) * hsNormSq (rankOne x y) := by
  rw [← norm_mulVecE_Qm_sq, hsNormSq_rankOne]
  by_cases hx : x = 0
  · have h : rankOne x y = 0 := by ext p q; simp [hx, rankOne]
    rw [h, vec_zero, mulVecE_zero]
    simp [hx]
  by_cases hy : y = 0
  · have h : rankOne x y = 0 := by ext p q; simp [hy, rankOne]
    rw [h, vec_zero, mulVecE_zero]
    simp [hy]
  have hx0 : ‖x‖ ≠ 0 := by simpa using hx
  have hy0 : ‖y‖ ≠ 0 := by simpa using hy
  let a : ℂ := (‖x‖ : ℂ)⁻¹
  let b : ℂ := (‖y‖ : ℂ)⁻¹
  have hna : ‖a • x‖ = 1 := by
    simp [a, norm_smul, norm_inv, hx0]
  have hnb : ‖b • bar y‖ = 1 := by
    simp [b, norm_smul, norm_inv, norm_bar, hy0]
  have h := norm_Qm_tensorOuter_unit_le (a • x) (b • bar y) hna hnb
  rw [tensorOuter_smul_smul, vec_smul, mulVecE_smul, norm_smul, tensorOuter_eq_rankOne_bar] at h
  have hbar : bar (bar y) = y := by ext p; simp
  rw [hbar] at h
  simp only [a, b, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg x), abs_of_nonneg (norm_nonneg y), ← mul_inv, mul_pow,
    inv_pow] at h
  exact (inv_mul_le_iff₀ (by positivity)).mp h |>.trans_eq (mul_comm _ _)

/-- The rank-one quadratic form on a diagonal tester is determined by the
purity of either partial trace. -/
theorem qform_Qm_rankOne_bar_self
    [DecidableEq U] [DecidableEq V] (x : EuclideanSpace ℂ (U × V)) :
    (qform Qm (vec (rankOne x (bar x)))).re =
      ((‖x‖ ^ 2) ^ 2 - hsNormSq (ptraceU (rankOne x x))) / 2 := by
  have h := rankOne_partialTrace_defect_eq x x
  rw [inner_self_complex, Complex.normSq_ofReal, ← hsNormSq_ptraces_rankOne_self x,
    norm_mulVecE_Qm_sq, tensorOuter_eq_rankOne_bar] at h
  nlinarith only [h]

end RankOne

end RankR
