/-
Sharpness of the rank-two Choi constant.

`ChoiTwoBound J β` is an upper bound, and monotone in `β` (`choiTwoBound_mono`):
it holds at `10^6` whenever it holds at all, so by itself it names no number.
`ChoiTwoAttained J β` is the dual condition, that the bound is met with equality
at some nonzero operator of rank at most two.  `le_of_choiTwoAttained` is the
leastness principle the pair generates --- an attained constant lies below every
valid one --- and the two together pin `β`, which is what
`choiTwoBound_skewKraus_iff` states for the double-skew family.

The witness is one rank-two operator.  Write `N = J_U ⊗ J_V` for an elementary
tensor of rotation generators and `P` for a rank-two orthogonal projection; since
`N` is unitary, `M = NP` has its two singular values equal, which is the equality
case of the Ky Fan estimate behind `‖Qm‖_{S(2)} = ½`.  Written in coordinates `M`
has two nonzero entries, and the collapse is visible directly: `swV` exchanges
them, `swU` carries both off the support, so the four-term alternating sum of
`qform_Qm_eq` contributes `2` at each and the normalization `4⁻¹` leaves `1`,
against `hsNormSq M = 2`.

Consequence: `β₂(Λ_U ⊗ Λ_V) = 1`, as an equality.
-/
import RankR.Core.PartialTrace.BlockPositivity
import RankR.Core.PartialTrace.Optimality
import RankR.Core.PartialTrace.Main

namespace RankR

open Matrix Finset ComplexConjugate

/-! ## Attainment, and the leastness it generates -/

section Attained

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- `β` is **attained** by the rank-two Choi form of `J`: some nonzero operator of
rank at most two meets `ChoiTwoBound` with equality.

Stated in the same unrolled two-term shape as `ChoiTwoBound`, so the two compose
without a translation step. -/
def ChoiTwoAttained (J : Matrix (W × W) (W × W) ℂ) (β : ℝ) : Prop :=
  ∃ u₁ v₁ u₂ v₂ : EuclideanSpace ℂ W,
    rankOne u₁ v₁ + rankOne u₂ v₂ ≠ 0 ∧
      (qform J (vec (rankOne u₁ v₁ + rankOne u₂ v₂))).re
        = 2 * β * hsNormSq (rankOne u₁ v₁ + rankOne u₂ v₂)

omit [DecidableEq W] in
/-- **An attained constant is least.**  The witness of the attainment has positive
Hilbert-Schmidt norm, so the equality it satisfies and the inequality supplied by
any valid constant may be divided by it. -/
theorem le_of_choiTwoAttained {J : Matrix (W × W) (W × W) ℂ} {β β' : ℝ}
    (ha : ChoiTwoAttained J β) (hb : ChoiTwoBound J β') : β ≤ β' := by
  obtain ⟨u₁, v₁, u₂, v₂, hne, heq⟩ := ha
  have hpos : 0 < hsNormSq (rankOne u₁ v₁ + rankOne u₂ v₂) := hsNormSq_pos hne
  have hle := hb u₁ v₁ u₂ v₂
  rw [heq] at hle
  nlinarith

omit [DecidableEq W] in
/-- Attainment is positively homogeneous, matching `choiTwoBound_smul`: the same
witness serves for the rescaled operator. -/
theorem choiTwoAttained_smul {J : Matrix (W × W) (W × W) ℂ} {β t : ℝ}
    (h : ChoiTwoAttained J β) : ChoiTwoAttained ((t : ℂ) • J) (t * β) := by
  obtain ⟨u₁, v₁, u₂, v₂, hne, heq⟩ := h
  refine ⟨u₁, v₁, u₂, v₂, hne, ?_⟩
  rw [qform_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    heq]
  ring

omit [DecidableEq W] in
/-- The unrolled two-term attainment predicate is the level-two instance of
`ChoiKAttained`. -/
theorem choiKAttained_two_of_choiTwoAttained
    {J : Matrix (W × W) (W × W) ℂ} {β : ℝ}
    (h : ChoiTwoAttained J β) :
    ChoiKAttained J 2 β := by
  obtain ⟨u₁, v₁, u₂, v₂, hne, heq⟩ := h
  refine ⟨![u₁, u₂], ![v₁, v₂], ?_, ?_⟩
  · simpa [Fin.sum_univ_two] using hne
  · simpa [Fin.sum_univ_two] using heq

end Attained

/-! ## The extremizer for the double antisymmetrizer -/

section Witness

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]

/-- The extremizing operator `M = N P`, in coordinates: it sends `(a₀, b₀)` to
`(a₁, b₁)` and `(a₀, b₁)` to `-(a₁, b₀)`, and kills everything else. -/
noncomputable def sharpWit (a₀ a₁ : U) (b₀ b₁ : V) : Matrix (U × V) (U × V) ℂ :=
  rankOne (eBasis (a₁, b₁)) (eBasis (a₀, b₀))
    + rankOne (-(eBasis (a₁, b₀) : EuclideanSpace ℂ (U × V))) (eBasis (a₀, b₁))

omit [Fintype U] [Fintype V] in
/-- The two nonzero entries of the extremizer. -/
theorem sharpWit_apply (a₀ a₁ : U) (b₀ b₁ : V) (p q : U × V) :
    sharpWit a₀ a₁ b₀ b₁ p q
      = (if p = (a₁, b₁) then (1 : ℂ) else 0) * (if q = (a₀, b₀) then 1 else 0)
        - (if p = (a₁, b₀) then (1 : ℂ) else 0) * (if q = (a₀, b₁) then 1 else 0) := by
  simp only [sharpWit, Matrix.add_apply, rankOne, Matrix.of_apply, PiLp.neg_apply,
    eBasis_apply, apply_ite (starRingEnd ℂ), map_one, map_zero]
  ring

/-- The support of the extremizer: the two index points carrying its entries. -/
private def wit₁ (a₀ a₁ : U) (b₀ b₁ : V) : Idx U V := ((a₁, b₁), (a₀, b₀))

private def wit₂ (a₀ a₁ : U) (b₀ b₁ : V) : Idx U V := ((a₁, b₀), (a₀, b₁))

omit [Fintype U] [Fintype V] in
/-- The vectorized extremizer is the difference of the two indicators of its
support. -/
theorem vec_sharpWit (a₀ a₁ : U) (b₀ b₁ : V) (X : Idx U V) :
    vec (sharpWit a₀ a₁ b₀ b₁) X
      = (if X = wit₁ a₀ a₁ b₀ b₁ then (1 : ℂ) else 0)
        - (if X = wit₂ a₀ a₁ b₀ b₁ then 1 else 0) := by
  show sharpWit a₀ a₁ b₀ b₁ X.1 X.2 = _
  rw [sharpWit_apply, wit₁, wit₂]
  by_cases hbb : b₀ = b₁
  · subst hbb
    by_cases h1 : X.1 = (a₁, b₀) <;> by_cases h2 : X.2 = (a₀, b₀) <;>
      simp [Prod.ext_iff, h1, h2]
  · by_cases h1 : X.1 = (a₁, b₁) <;> by_cases h2 : X.2 = (a₀, b₀) <;>
      by_cases h3 : X.1 = (a₁, b₀) <;> by_cases h4 : X.2 = (a₀, b₁) <;>
        simp [Prod.ext_iff, h1, h2, h3, h4, hbb]

/-- The squared Hilbert-Schmidt norm of the extremizer is `2`: its two entries are
distinct index points, because the two `V`-labels differ. -/
theorem hsNormSq_sharpWit {a₀ a₁ : U} {b₀ b₁ : V} (hb : b₀ ≠ b₁) :
    hsNormSq (sharpWit a₀ a₁ b₀ b₁) = 2 := by
  have hne : wit₁ a₀ a₁ b₀ b₁ ≠ wit₂ a₀ a₁ b₀ b₁ := by
    simp [wit₁, wit₂, Prod.ext_iff]; exact fun _ => hb
  have hterm : ∀ X : Idx U V, Complex.normSq (vec (sharpWit a₀ a₁ b₀ b₁) X)
      = (if X = wit₁ a₀ a₁ b₀ b₁ then (1 : ℝ) else 0)
        + (if X = wit₂ a₀ a₁ b₀ b₁ then 1 else 0) := by
    intro X
    rw [vec_sharpWit]
    by_cases h1 : X = wit₁ a₀ a₁ b₀ b₁ <;> by_cases h2 : X = wit₂ a₀ a₁ b₀ b₁ <;>
      simp_all [Complex.normSq]
  have hsum : hsNormSq (sharpWit a₀ a₁ b₀ b₁)
      = ∑ X : Idx U V, Complex.normSq (vec (sharpWit a₀ a₁ b₀ b₁) X) := by
    rw [Fintype.sum_prod_type]
    rfl
  rw [hsum, Finset.sum_congr rfl fun X _ => hterm X, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (wit₁ a₀ a₁ b₀ b₁) (fun _ => (1 : ℝ)),
    Finset.sum_ite_eq' Finset.univ (wit₂ a₀ a₁ b₀ b₁) (fun _ => (1 : ℝ))]
  simp only [Finset.mem_univ, ↓reduceIte]
  norm_num

omit [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] in
/-- `swV` exchanges the two support points: this is the whole of the extremality.
The `V`-swap is a symmetry of the support, so the alternating sum reinforces
rather than cancels. -/
private theorem swV_wit₁ (a₀ a₁ : U) (b₀ b₁ : V) :
    swV (wit₁ a₀ a₁ b₀ b₁) = wit₂ a₀ a₁ b₀ b₁ := rfl

omit [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] in
private theorem swV_wit₂ (a₀ a₁ : U) (b₀ b₁ : V) :
    swV (wit₂ a₀ a₁ b₀ b₁) = wit₁ a₀ a₁ b₀ b₁ := rfl

/-- **The extremizer meets the `S(2)` bound with equality**: the quadratic form of
the double antisymmetrizer at the vectorized witness is `1`, against
`hsNormSq = 2`, so the ratio is the `½` of `‖Qm‖_{S(2)}`.

The four-term alternating sum of `qform_Qm_eq` is evaluated pointwise.  Off the
two support points every term vanishes.  At each support point `swV` returns the
other one with the opposite sign, contributing `+1` where the diagonal term
contributes `+1`, while both `swU`-images lie off the support because the two
`U`-labels differ.  Each support point therefore contributes `2`, and `4⁻¹ · 4`
is `1`. -/
theorem qform_Qm_sharpWit {a₀ a₁ : U} {b₀ b₁ : V} (ha : a₀ ≠ a₁) (hb : b₀ ≠ b₁) :
    qform (Qm : Matrix (Idx U V) (Idx U V) ℂ) (vec (sharpWit a₀ a₁ b₀ b₁)) = 1 := by
  have h12 : wit₁ a₀ a₁ b₀ b₁ ≠ wit₂ a₀ a₁ b₀ b₁ := by
    simp [wit₁, wit₂, Prod.ext_iff]; exact fun _ => hb
  -- the six values of the vectorized witness that the alternating sum can see
  have e1 : vec (sharpWit a₀ a₁ b₀ b₁) (wit₁ a₀ a₁ b₀ b₁) = 1 := by
    rw [vec_sharpWit, if_pos rfl, if_neg h12]; ring
  have e2 : vec (sharpWit a₀ a₁ b₀ b₁) (wit₂ a₀ a₁ b₀ b₁) = -1 := by
    rw [vec_sharpWit, if_neg (Ne.symm h12), if_pos rfl]; ring
  have e3 : vec (sharpWit a₀ a₁ b₀ b₁) (swU (wit₁ a₀ a₁ b₀ b₁)) = 0 := by
    rw [vec_sharpWit]; simp [wit₁, wit₂, swU, Prod.ext_iff, ha]
  have e4 : vec (sharpWit a₀ a₁ b₀ b₁) (swV (swU (wit₁ a₀ a₁ b₀ b₁))) = 0 := by
    rw [vec_sharpWit]; simp [wit₁, wit₂, swU, swV, Prod.ext_iff, ha]
  have e5 : vec (sharpWit a₀ a₁ b₀ b₁) (swU (wit₂ a₀ a₁ b₀ b₁)) = 0 := by
    rw [vec_sharpWit]; simp [wit₁, wit₂, swU, Prod.ext_iff, ha]
  have e6 : vec (sharpWit a₀ a₁ b₀ b₁) (swV (swU (wit₂ a₀ a₁ b₀ b₁))) = 0 := by
    rw [vec_sharpWit]; simp [wit₁, wit₂, swU, swV, Prod.ext_iff, ha]
  have hsummand : ∀ X : Idx U V,
      conj (vec (sharpWit a₀ a₁ b₀ b₁) X) *
          (vec (sharpWit a₀ a₁ b₀ b₁) X - vec (sharpWit a₀ a₁ b₀ b₁) (swU X)
            - vec (sharpWit a₀ a₁ b₀ b₁) (swV X)
            + vec (sharpWit a₀ a₁ b₀ b₁) (swV (swU X)))
        = 2 * (if X = wit₁ a₀ a₁ b₀ b₁ then (1 : ℂ) else 0)
          + 2 * (if X = wit₂ a₀ a₁ b₀ b₁ then 1 else 0) := by
    intro X
    by_cases h1 : X = wit₁ a₀ a₁ b₀ b₁
    · rw [h1, e1, e3, swV_wit₁, e2, e4, if_pos rfl, if_neg h12]
      norm_num
    · by_cases h2 : X = wit₂ a₀ a₁ b₀ b₁
      · rw [h2, e2, e5, swV_wit₂, e1, e6, if_neg (Ne.symm h12), if_pos rfl]
        norm_num
      · have h0 : vec (sharpWit a₀ a₁ b₀ b₁) X = 0 := by
          rw [vec_sharpWit, if_neg h1, if_neg h2]; ring
        rw [h0, if_neg h1, if_neg h2]
        simp
  rw [qform_Qm_eq, Finset.sum_congr rfl fun X _ => hsummand X]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (wit₁ a₀ a₁ b₀ b₁) (fun _ => (2 : ℂ)),
    Finset.sum_ite_eq' Finset.univ (wit₂ a₀ a₁ b₀ b₁) (fun _ => (2 : ℂ)),
    Finset.mem_univ, if_true]
  norm_num

/-! ## The rank-three truncation -/

/-- Three of the four signed matrix units in one elementary double-skew
operator.  Its three nonzero singular values are all one. -/
noncomputable def sharpWitThree (a₀ a₁ : U) (b₀ b₁ : V) :
    Matrix (U × V) (U × V) ℂ :=
  sharpWit a₀ a₁ b₀ b₁
    + rankOne (-(eBasis (a₀, b₁) : EuclideanSpace ℂ (U × V)))
        (eBasis (a₁, b₀))

/-- The third support point of the rank-three truncation. -/
private def wit₃ (a₀ a₁ : U) (b₀ b₁ : V) : Idx U V :=
  ((a₀, b₁), (a₁, b₀))

/-- The omitted fourth point in its double-swap orbit. -/
private def wit₄ (a₀ a₁ : U) (b₀ b₁ : V) : Idx U V :=
  ((a₀, b₀), (a₁, b₁))

omit [Fintype U] [Fintype V] in
/-- A signed rank-one matrix unit vectorizes to a signed coordinate vector. -/
private theorem vec_rankOne_neg_eBasis (p q : U × V) (X : Idx U V) :
    vec (rankOne (-(eBasis p : EuclideanSpace ℂ (U × V))) (eBasis q)) X
      = if X = (p, q) then (-1 : ℂ) else 0 := by
  by_cases hX : X = (p, q)
  · subst X
    simp [rankOne]
  · by_cases hp : X.1 = p
    · by_cases hq : X.2 = q
      · exact (hX (Prod.ext hp hq)).elim
      · simp [rankOne, hp, hq, hX]
    · simp [rankOne, hp, hX]

omit [Fintype U] [Fintype V] in
/-- The vectorized rank-three witness has coefficients `1,-1,-1` on its three
support points. -/
theorem vec_sharpWitThree (a₀ a₁ : U) (b₀ b₁ : V) (X : Idx U V) :
    vec (sharpWitThree a₀ a₁ b₀ b₁) X
      = (if X = wit₁ a₀ a₁ b₀ b₁ then (1 : ℂ) else 0)
        - (if X = wit₂ a₀ a₁ b₀ b₁ then 1 else 0)
        - (if X = wit₃ a₀ a₁ b₀ b₁ then 1 else 0) := by
  rw [sharpWitThree, vec_add, PiLp.add_apply, vec_sharpWit]
  rw [vec_rankOne_neg_eBasis]
  by_cases h3 : X = wit₃ a₀ a₁ b₀ b₁
  · have h3' : X = ((a₀, b₁), (a₁, b₀)) := by simpa [wit₃] using h3
    rw [if_pos h3', if_pos h3]
    abel
  · have h3' : X ≠ ((a₀, b₁), (a₁, b₀)) := by simpa [wit₃] using h3
    rw [if_neg h3', if_neg h3]
    simp

/-- The squared Hilbert--Schmidt norm of the rank-three truncation is three. -/
theorem hsNormSq_sharpWitThree {a₀ a₁ : U} {b₀ b₁ : V}
    (ha : a₀ ≠ a₁) (hb : b₀ ≠ b₁) :
    hsNormSq (sharpWitThree a₀ a₁ b₀ b₁) = 3 := by
  have h12 : wit₁ a₀ a₁ b₀ b₁ ≠ wit₂ a₀ a₁ b₀ b₁ := by
    simp only [wit₁, wit₂, ne_eq, Prod.ext_iff, true_and, not_and]
    exact fun _ => hb
  have h13 : wit₁ a₀ a₁ b₀ b₁ ≠ wit₃ a₀ a₁ b₀ b₁ := by
    simp [wit₁, wit₃, Prod.ext_iff, ha]
  have h23 : wit₂ a₀ a₁ b₀ b₁ ≠ wit₃ a₀ a₁ b₀ b₁ := by
    simp [wit₂, wit₃, Prod.ext_iff, ha]
  have hterm : ∀ X : Idx U V,
      Complex.normSq (vec (sharpWitThree a₀ a₁ b₀ b₁) X)
        = (if X = wit₁ a₀ a₁ b₀ b₁ then (1 : ℝ) else 0)
          + (if X = wit₂ a₀ a₁ b₀ b₁ then 1 else 0)
          + (if X = wit₃ a₀ a₁ b₀ b₁ then 1 else 0) := by
    intro X
    rw [vec_sharpWitThree]
    by_cases h1 : X = wit₁ a₀ a₁ b₀ b₁
      <;> by_cases h2 : X = wit₂ a₀ a₁ b₀ b₁
      <;> by_cases h3 : X = wit₃ a₀ a₁ b₀ b₁
      <;> simp_all [Complex.normSq]
  have hsum : hsNormSq (sharpWitThree a₀ a₁ b₀ b₁)
      = ∑ X : Idx U V,
          Complex.normSq (vec (sharpWitThree a₀ a₁ b₀ b₁) X) := by
    rw [Fintype.sum_prod_type]
    rfl
  rw [hsum, Finset.sum_congr rfl fun X _ => hterm X,
    Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (wit₁ a₀ a₁ b₀ b₁) (fun _ => (1 : ℝ)),
    Finset.sum_ite_eq' Finset.univ (wit₂ a₀ a₁ b₀ b₁) (fun _ => (1 : ℝ)),
    Finset.sum_ite_eq' Finset.univ (wit₃ a₀ a₁ b₀ b₁) (fun _ => (1 : ℝ))]
  simp only [Finset.mem_univ, ↓reduceIte]
  norm_num

/-- The rank-three truncation is admissible at every level at least three. -/
theorem rank_sharpWitThree_le (a₀ a₁ : U) (b₀ b₁ : V) :
    (sharpWitThree a₀ a₁ b₀ b₁).rank ≤ 3 := by
  apply (rank_le_iff_exists_sum_rankOne (W := U × V) (k := 3)
    (sharpWitThree a₀ a₁ b₀ b₁)).mpr
  refine ⟨(fun i : Fin 3 => ![eBasis (a₁, b₁), -(eBasis (a₁, b₀)),
      -(eBasis (a₀, b₁))] i),
    (fun i : Fin 3 =>
      ![eBasis (a₀, b₀), eBasis (a₀, b₁), eBasis (a₁, b₀)] i), ?_⟩
  simp only [sharpWitThree, sharpWit, Nat.succ_eq_add_one,
    Nat.reduceAdd, Fin.sum_univ_succ, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Finset.univ_unique, Fin.default_eq_zero,
    Matrix.cons_val_fin_one, Finset.sum_const, Finset.card_singleton,
    one_smul]
  abel

/-- The rank-three truncation is nonzero. -/
theorem sharpWitThree_ne_zero {a₀ a₁ : U} {b₀ b₁ : V}
    (ha : a₀ ≠ a₁) (hb : b₀ ≠ b₁) :
    sharpWitThree a₀ a₁ b₀ b₁ ≠ 0 := by
  intro h
  have h3 := hsNormSq_sharpWitThree ha hb
  rw [h] at h3
  simp [hsNormSq] at h3

omit [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] in
private theorem swU_wit₁_three (a₀ a₁ : U) (b₀ b₁ : V) :
    swU (wit₁ a₀ a₁ b₀ b₁) = wit₃ a₀ a₁ b₀ b₁ := rfl

omit [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] in
private theorem swVU_wit₁_three (a₀ a₁ : U) (b₀ b₁ : V) :
    swV (swU (wit₁ a₀ a₁ b₀ b₁)) = wit₄ a₀ a₁ b₀ b₁ := rfl

omit [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] in
private theorem swU_wit₂_three (a₀ a₁ : U) (b₀ b₁ : V) :
    swU (wit₂ a₀ a₁ b₀ b₁) = wit₄ a₀ a₁ b₀ b₁ := rfl

omit [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] in
private theorem swVU_wit₂_three (a₀ a₁ : U) (b₀ b₁ : V) :
    swV (swU (wit₂ a₀ a₁ b₀ b₁)) = wit₃ a₀ a₁ b₀ b₁ := rfl

omit [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] in
private theorem swU_wit₃_three (a₀ a₁ : U) (b₀ b₁ : V) :
    swU (wit₃ a₀ a₁ b₀ b₁) = wit₁ a₀ a₁ b₀ b₁ := rfl

omit [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] in
private theorem swV_wit₃_three (a₀ a₁ : U) (b₀ b₁ : V) :
    swV (wit₃ a₀ a₁ b₀ b₁) = wit₄ a₀ a₁ b₀ b₁ := rfl

omit [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] in
private theorem swV_wit₄_three (a₀ a₁ : U) (b₀ b₁ : V) :
    swV (wit₄ a₀ a₁ b₀ b₁) = wit₃ a₀ a₁ b₀ b₁ := rfl

omit [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] in
private theorem swVU_wit₃_three (a₀ a₁ : U) (b₀ b₁ : V) :
    swV (swU (wit₃ a₀ a₁ b₀ b₁)) = wit₂ a₀ a₁ b₀ b₁ := rfl

/-- The rank-three truncation attains the coefficient `3/4` in the
low-rank quadratic-form bound for `Qm`. -/
theorem qform_Qm_sharpWitThree {a₀ a₁ : U} {b₀ b₁ : V}
    (ha : a₀ ≠ a₁) (hb : b₀ ≠ b₁) :
    qform (Qm : Matrix (Idx U V) (Idx U V) ℂ)
      (vec (sharpWitThree a₀ a₁ b₀ b₁)) = 9 / 4 := by
  have h12 : wit₁ a₀ a₁ b₀ b₁ ≠ wit₂ a₀ a₁ b₀ b₁ := by
    simp only [wit₁, wit₂, ne_eq, Prod.ext_iff, true_and, not_and]
    exact fun _ => hb
  have h13 : wit₁ a₀ a₁ b₀ b₁ ≠ wit₃ a₀ a₁ b₀ b₁ := by
    simp [wit₁, wit₃, Prod.ext_iff, ha]
  have h23 : wit₂ a₀ a₁ b₀ b₁ ≠ wit₃ a₀ a₁ b₀ b₁ := by
    simp [wit₂, wit₃, Prod.ext_iff, ha]
  have h41 : wit₄ a₀ a₁ b₀ b₁ ≠ wit₁ a₀ a₁ b₀ b₁ := by
    simp [wit₄, wit₁, Prod.ext_iff, ha]
  have h42 : wit₄ a₀ a₁ b₀ b₁ ≠ wit₂ a₀ a₁ b₀ b₁ := by
    simp [wit₄, wit₂, Prod.ext_iff, ha]
  have h43 : wit₄ a₀ a₁ b₀ b₁ ≠ wit₃ a₀ a₁ b₀ b₁ := by
    intro h
    have h' := congrArg (fun X : Idx U V => X.1.2) h
    simp [wit₄, wit₃] at h'
    exact hb h'
  have e1 :
      vec (sharpWitThree a₀ a₁ b₀ b₁) (wit₁ a₀ a₁ b₀ b₁) = 1 := by
    rw [vec_sharpWitThree, if_pos rfl, if_neg h12, if_neg h13]
    ring
  have e2 :
      vec (sharpWitThree a₀ a₁ b₀ b₁) (wit₂ a₀ a₁ b₀ b₁) = -1 := by
    rw [vec_sharpWitThree, if_neg (Ne.symm h12), if_pos rfl, if_neg h23]
    ring
  have e3 :
      vec (sharpWitThree a₀ a₁ b₀ b₁) (wit₃ a₀ a₁ b₀ b₁) = -1 := by
    rw [vec_sharpWitThree, if_neg (Ne.symm h13),
      if_neg (Ne.symm h23), if_pos rfl]
    ring
  have e4 :
      vec (sharpWitThree a₀ a₁ b₀ b₁) (wit₄ a₀ a₁ b₀ b₁) = 0 := by
    rw [vec_sharpWitThree, if_neg h41, if_neg h42, if_neg h43]
    ring
  have hsummand : ∀ X : Idx U V,
      conj (vec (sharpWitThree a₀ a₁ b₀ b₁) X) *
          (vec (sharpWitThree a₀ a₁ b₀ b₁) X
            - vec (sharpWitThree a₀ a₁ b₀ b₁) (swU X)
            - vec (sharpWitThree a₀ a₁ b₀ b₁) (swV X)
            + vec (sharpWitThree a₀ a₁ b₀ b₁) (swV (swU X)))
        = 3 * (if X = wit₁ a₀ a₁ b₀ b₁ then (1 : ℂ) else 0)
          + 3 * (if X = wit₂ a₀ a₁ b₀ b₁ then 1 else 0)
          + 3 * (if X = wit₃ a₀ a₁ b₀ b₁ then 1 else 0) := by
    intro X
    by_cases h1 : X = wit₁ a₀ a₁ b₀ b₁
    · rw [h1, e1, swU_wit₁_three, e3, swV_wit₁, e2,
        swV_wit₃_three, e4, if_pos rfl, if_neg h12, if_neg h13]
      norm_num
    · by_cases h2 : X = wit₂ a₀ a₁ b₀ b₁
      · rw [h2, e2, swU_wit₂_three, e4, swV_wit₂, e1,
          swV_wit₄_three, e3, if_neg (Ne.symm h12), if_pos rfl,
          if_neg h23]
        norm_num
      · by_cases h3 : X = wit₃ a₀ a₁ b₀ b₁
        · rw [h3, e3, swU_wit₃_three, e1, swV_wit₃_three, e4,
            swV_wit₁, e2, if_neg (Ne.symm h13),
            if_neg (Ne.symm h23), if_pos rfl]
          norm_num
        · have h0 : vec (sharpWitThree a₀ a₁ b₀ b₁) X = 0 := by
            rw [vec_sharpWitThree, if_neg h1, if_neg h2, if_neg h3]
            ring
          rw [h0, if_neg h1, if_neg h2, if_neg h3]
          simp
  rw [qform_Qm_eq, Finset.sum_congr rfl fun X _ => hsummand X]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (wit₁ a₀ a₁ b₀ b₁) (fun _ => (3 : ℂ)),
    Finset.sum_ite_eq' Finset.univ (wit₂ a₀ a₁ b₀ b₁) (fun _ => (3 : ℂ)),
    Finset.sum_ite_eq' Finset.univ (wit₃ a₀ a₁ b₀ b₁) (fun _ => (3 : ℂ)),
    Finset.mem_univ, if_true]
  norm_num

/-- `1/4` is attained by `Qm` at level three. -/
theorem choiKAttained_Qm_three {a₀ a₁ : U} {b₀ b₁ : V}
    (ha : a₀ ≠ a₁) (hb : b₀ ≠ b₁) :
    ChoiKAttained (Qm : Matrix (Idx U V) (Idx U V) ℂ) 3 (1 / 4) := by
  apply choiKAttained_of_matrix (rank_sharpWitThree_le a₀ a₁ b₀ b₁)
    (sharpWitThree_ne_zero ha hb)
  rw [qform_Qm_sharpWitThree ha hb, hsNormSq_sharpWitThree ha hb]
  norm_num

/-! ## The constant of the double-skew family is exactly `4` -/

/-- The extremizer is nonzero, since its Hilbert-Schmidt norm is `2`. -/
theorem sharpWit_ne_zero {a₀ a₁ : U} {b₀ b₁ : V} (hb : b₀ ≠ b₁) :
    sharpWit a₀ a₁ b₀ b₁ ≠ 0 := by
  intro h
  have h2 := hsNormSq_sharpWit (a₀ := a₀) (a₁ := a₁) hb
  rw [h] at h2
  simp [hsNormSq] at h2

/-- The extremizer is a sum of two rank-one operators, so it is admissible as a
witness for `ChoiTwoAttained` without unfolding its definition. -/
theorem choiTwoAttained_of_sharpWit {J : Matrix (Idx U V) (Idx U V) ℂ} {β : ℝ}
    {a₀ a₁ : U} {b₀ b₁ : V} (hne : sharpWit a₀ a₁ b₀ b₁ ≠ 0)
    (heq : (qform J (vec (sharpWit a₀ a₁ b₀ b₁))).re
      = 2 * β * hsNormSq (sharpWit a₀ a₁ b₀ b₁)) :
    ChoiTwoAttained J β :=
  ⟨eBasis (a₁, b₁), eBasis (a₀, b₀), -(eBasis (a₁, b₀)), eBasis (a₀, b₁), hne, heq⟩

/-- **`¼` is attained by the double antisymmetrizer.**  With the upper bound that
`Equivalence.lean` derives from Autonne-Takagi, this is `‖Qm‖_{S(2)} = ½`. -/
theorem choiTwoAttained_Qm {a₀ a₁ : U} {b₀ b₁ : V} (ha : a₀ ≠ a₁) (hb : b₀ ≠ b₁) :
    ChoiTwoAttained (Qm : Matrix (Idx U V) (Idx U V) ℂ) (1 / 4) := by
  refine choiTwoAttained_of_sharpWit (a₀ := a₀) (a₁ := a₁) (b₀ := b₀) (b₁ := b₁)
    (sharpWit_ne_zero hb) ?_
  rw [qform_Qm_sharpWit ha hb, hsNormSq_sharpWit hb]
  norm_num

/-- **`4` is attained by the Choi operator of `Λ_U ⊗ Λ_V`.**  The Choi operator is
`16 Qm`, and attainment rescales with the operator. -/
theorem choiTwoAttained_skewKraus {a₀ a₁ : U} {b₀ b₁ : V} (ha : a₀ ≠ a₁) (hb : b₀ ≠ b₁) :
    ChoiTwoAttained (choiOf (skewKraus (U := U) (V := V))) 4 := by
  rw [choiOf_skewKraus, show (16 : ℂ) = ((16 : ℝ) : ℂ) by norm_num,
    show (4 : ℝ) = 16 * (1 / 4) by norm_num]
  exact choiTwoAttained_smul (choiTwoAttained_Qm ha hb)

omit [DecidableEq U] [DecidableEq V] in
/-- The rank-two bound is monotone in its constant, which is precisely why the
bound alone cannot determine one. -/
theorem choiTwoBound_mono {J : Matrix ((U × V) × (U × V)) ((U × V) × (U × V)) ℂ} {β β' : ℝ}
    (h : ChoiTwoBound J β) (hle : β ≤ β') : ChoiTwoBound J β' := by
  intro u₁ v₁ u₂ v₂
  have hn := hsNormSq_nonneg (rankOne u₁ v₁ + rankOne u₂ v₂)
  have := h u₁ v₁ u₂ v₂
  nlinarith

/-- **`β₂(Λ_U ⊗ Λ_V) = 1`.**

In the `Phi4` normalization the statement reads `β₂ = 4`, and it is here in the
only form that determines a number: the valid constants for the family are
exactly the reals `≥ 4`.  The forward direction is `le_of_choiTwoAttained` at the
extremizer; the reverse is `choiTwoBound_holds` weakened by monotonicity.

Two distinct labels are needed in each factor, and that is not an artifact: for
`dim U < 2` or `dim V < 2` the double-skew subspace is zero and every constant is
valid. -/
theorem choiTwoBound_skewKraus_iff {a₀ a₁ : U} {b₀ b₁ : V} (ha : a₀ ≠ a₁) (hb : b₀ ≠ b₁)
    (β : ℝ) : ChoiTwoBound (choiOf (skewKraus (U := U) (V := V))) β ↔ 4 ≤ β :=
  ⟨fun h => le_of_choiTwoAttained (choiTwoAttained_skewKraus ha hb) h,
    fun h => choiTwoBound_mono choiTwoBound_holds h⟩

end Witness

/-! ## The block positivity of `J(Ψ_r)` is not strict -/

section BlockBoundary

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]

/-- **`J(Ψ_r)` sits exactly on the boundary of `r`-block positivity.**

`isBlockPositive_psiChoi` gives `0 ≤ ⟪vec C, J(Ψ_r) vec C⟫` for every `C` of rank
at most `r`; the extremizer of `Optimal.lean` makes it `0`.  So the block
positivity certified by Theorem 1.1 cannot be improved to a strict inequality,
and no positive multiple of the identity can be subtracted from `J(Ψ_r)` while
keeping it.

This is the sharpness of the *conclusion* at the double-skew instance.  The
sharpness of the amplification *coefficient* `(r-1)β₂` for a general `Φ` is a
different statement, needing a family for which that coefficient is attained ---
the edge-Kraus graph family of `paper/derivation-graph-inclusion.tex` is one. -/
theorem re_qform_psiChoi_projWit {r : ℕ} {S : Finset U} (hS : S.card = r)
    (x₀ x₁ : V) :
    (qform (psiChoi (U := U) (V := V) r) (vec (projWit S x₀ x₁))).re = 0 := by
  rw [re_qform_psiChoi]
  linarith [projWit_bound_eq (U := U) S x₀ x₁ hS]

end BlockBoundary

end RankR
