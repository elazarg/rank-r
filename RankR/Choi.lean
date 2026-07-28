/-
The Choi operator of a Kraus family, and the amplification step of section 2.

A completely positive map `Φ` with Kraus family `{Aₐ}` has Choi operator

  `J(Φ) = ∑ₐ |vec Aₐ⟩⟨vec Aₐ|`,

the same operator for every Kraus family of `Φ`.  Its rank-two operator norm is
recorded as `β`:

  `ChoiTwoBound J β  ↔  ⟪z, J z⟫ ≤ 2β‖z‖²  for every `z` of Schmidt rank ≤ 2`,

so that `β = ½‖J(Φ)‖_{S(2)}`.  Since `J` is linear in `Φ`, so is `β`, and a map
and its constant always carry the same scale.

Three hypotheses suffice for the amplification step of `lem:double-skew`: that
`K` lies in the span of the family, that `J(Φ)` obeys `ChoiTwoBound _ β`, and
that `x, y` are orthonormal.  The compression `K P` onto `span {x, y}` pairs with
`K` to `‖K P‖₂²`, expands along the Kraus index by Cauchy-Schwarz, and is
rank-two, so the three combine into

  `‖K x‖² + ‖K y‖² ≤ 2β ∑ₐ |cₐ|²`     (`norm_sq_pair_le_of_choiTwoBound`).

For the double-skew family `J` is `16 Qm` (`RankR.choiOf_skewKraus`), so
Fu-Gao-Park's `‖Qm‖_{S(2)} = ½` reads `β = 4`.
-/
import RankR.Kraus

namespace RankR

open Matrix Finset ComplexConjugate

/-! ## Rank-one algebra

Three identities about `|u⟩⟨v|` that the rank-two projection needs. -/

section HsAlgebra

variable {W : Type*} [Fintype W]

omit [Fintype W] in
/-- `(|u⟩⟨v|)ᴴ = |v⟩⟨u|`. -/
theorem rankOne_conjTranspose (u v : EuclideanSpace ℂ W) :
    (rankOne u v)ᴴ = rankOne v u := by
  ext p q
  simp [rankOne, Matrix.conjTranspose_apply, RCLike.star_def, mul_comm]

/-- `K |u⟩⟨v| = |Ku⟩⟨v|`. -/
theorem mul_rankOne (K : Matrix W W ℂ) (u v : EuclideanSpace ℂ W) :
    K * rankOne u v = rankOne (mulVecE K u) v := by
  ext p q
  simp [rankOne, Matrix.mul_apply, mulVecE_apply, Finset.sum_mul, mul_assoc]

/-- `|u⟩⟨v| |z⟩⟨w| = ⟪v,z⟫ · |u⟩⟨w|`. -/
theorem rankOne_mul_rankOne (u v z w : EuclideanSpace ℂ W) :
    rankOne u v * rankOne z w = (inner ℂ v z : ℂ) • rankOne u w := by
  ext p q
  simp only [rankOne, Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply,
    smul_eq_mul, PiLp.inner_apply, RCLike.inner_apply', Finset.sum_mul]
  exact Finset.sum_congr rfl fun r _ => by ring

end HsAlgebra

/-! ## Sesquilinearity of the Hilbert-Schmidt pairing

`Elementary.lean` has the `Fin s`-indexed bilinear expansion; the Kraus index is
an arbitrary `Fintype`, and only the first argument moves. -/

section Sesqui

variable {m n : Type*} [Fintype m] [Fintype n]

/-- `hsInner` is conjugate-homogeneous in its first argument. -/
theorem hsInner_smul_left (c : ℂ) (A B : Matrix m n ℂ) :
    hsInner (c • A) B = conj c * hsInner A B := by
  simp [hsInner, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.trace_smul,
    RCLike.star_def, smul_eq_mul]

/-- `hsInner` is additive in its first argument, over an arbitrary finite index. -/
theorem hsInner_sum_left {ι : Type*} [Fintype ι] (A : ι → Matrix m n ℂ) (B : Matrix m n ℂ) :
    hsInner (∑ a, A a) B = ∑ a, hsInner (A a) B := by
  simp only [hsInner, Matrix.conjTranspose_sum]
  rw [Matrix.sum_mul, Matrix.trace_sum]

end Sesqui

/-! ## The rank-two projection

`proj2 x y` is the orthogonal projection onto `span {x, y}` for an orthonormal
pair.  Compressing `K` by it produces a matrix of rank at most two whose squared
Hilbert-Schmidt norm is exactly the quantity to be bounded, and which pairs with
`K` to that same real number. -/

section Projection

variable {W : Type*} [Fintype W] {x y : EuclideanSpace ℂ W}

/-- The rank-two orthogonal projection onto `span {x, y}`. -/
noncomputable def proj2 (x y : EuclideanSpace ℂ W) : Matrix W W ℂ :=
  rankOne x x + rankOne y y

omit [Fintype W] in
theorem proj2_conjTranspose : (proj2 x y)ᴴ = proj2 x y := by
  simp [proj2, Matrix.conjTranspose_add, rankOne_conjTranspose]

theorem proj2_mul_self (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : inner ℂ x y = (0 : ℂ)) :
    proj2 x y * proj2 x y = proj2 x y := by
  have hyx : (inner ℂ y x : ℂ) = 0 := by
    rw [← inner_conj_symm, hxy, map_zero]
  have hxx : (inner ℂ x x : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hx]; norm_num
  have hyy : (inner ℂ y y : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hy]; norm_num
  simp only [proj2, Matrix.add_mul, Matrix.mul_add, rankOne_mul_rankOne,
    hxx, hyy, hxy, hyx, one_smul, zero_smul]
  abel

/-- `K P` is the two-term operator `|Kx⟩⟨x| + |Ky⟩⟨y|`; this is the unrolling of
"rank at most two" that `ChoiTwoBound` quantifies over. -/
theorem mul_proj2 (K : Matrix W W ℂ) (x y : EuclideanSpace ℂ W) :
    K * proj2 x y = rankOne (mulVecE K x) x + rankOne (mulVecE K y) y := by
  rw [proj2, Matrix.mul_add, mul_rankOne, mul_rankOne]

/-- `‖K P‖₂²` is the action of `K` on the orthonormal pair. -/
theorem hsNormSq_mul_proj2 (K : Matrix W W ℂ) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : inner ℂ x y = (0 : ℂ)) :
    hsNormSq (K * proj2 x y) = ‖mulVecE K x‖ ^ 2 + ‖mulVecE K y‖ ^ 2 := by
  have hyx : (inner ℂ y x : ℂ) = 0 := by rw [← inner_conj_symm, hxy, map_zero]
  have hxx : (inner ℂ x x : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hx]; norm_num
  have hyy : (inner ℂ y y : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hy]; norm_num
  rw [mul_proj2, ← Complex.ofReal_inj, ← hsInner_self, hsInner_add_left,
    hsInner_add_right, hsInner_add_right, hsInner_rankOne, hsInner_rankOne,
    hsInner_rankOne, hsInner_rankOne, hxy, hyx, hxx, hyy,
    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  push_cast
  simp

/-- `⟪K, K P⟫ = ‖K P‖₂²`, because `P` is a self-adjoint idempotent.  This is what
lets the compressed operator be tested against `K` itself. -/
theorem hsInner_mul_proj2 (K : Matrix W W ℂ) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : inner ℂ x y = (0 : ℂ)) :
    hsInner K (K * proj2 x y) = (hsNormSq (K * proj2 x y) : ℂ) := by
  rw [← hsInner_self]
  have e1 : hsInner K (K * proj2 x y) = (Kᴴ * K * proj2 x y).trace := by
    rw [hsInner, Matrix.mul_assoc]
  have e2 : hsInner (K * proj2 x y) (K * proj2 x y) = (Kᴴ * K * proj2 x y).trace := by
    rw [hsInner, Matrix.conjTranspose_mul, proj2_conjTranspose,
      show proj2 x y * Kᴴ * (K * proj2 x y) = proj2 x y * (Kᴴ * K * proj2 x y) by
        simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm,
      show Kᴴ * K * proj2 x y * proj2 x y = Kᴴ * K * (proj2 x y * proj2 x y) by
        simp only [Matrix.mul_assoc],
      proj2_mul_self hx hy hxy]
  rw [e1, e2]

end Projection

/-! ## The Choi operator of a Kraus family -/

section Choi

variable {W ι : Type*} [Fintype W] [Fintype ι]

/-- `J(Φ) = ∑ₐ |vec Aₐ⟩⟨vec Aₐ|`, the Choi operator of the completely positive
map with Kraus family `{Aₐ}`.

No minimality and no orthogonality of the family is assumed: this formula holds
for *every* Kraus family of `Φ`, which is what makes `β` below intrinsic to `Φ`
rather than to a choice of decomposition. -/
noncomputable def choiOf (A : ι → Matrix W W ℂ) : Matrix (W × W) (W × W) ℂ :=
  ∑ a, rankOne (vec (A a)) (vec (A a))

/-- The quadratic form of a Choi operator is the Bessel sum of the family. -/
theorem qform_choiOf (A : ι → Matrix W W ℂ) (v : EuclideanSpace ℂ (W × W)) :
    qform (choiOf A) v = ∑ a, ((Complex.normSq (inner ℂ (vec (A a)) v) : ℝ) : ℂ) := by
  rw [choiOf, qform_sum]
  exact Finset.sum_congr rfl fun a _ => qform_rankOne _ _

/-- The real part of the same, which is what the estimates consume. -/
theorem re_qform_choiOf (A : ι → Matrix W W ℂ) (v : EuclideanSpace ℂ (W × W)) :
    (qform (choiOf A) v).re = ∑ a, Complex.normSq (inner ℂ (vec (A a)) v) := by
  rw [qform_choiOf, Complex.re_sum]
  exact Finset.sum_congr rfl fun a _ => Complex.ofReal_re _

end Choi

/-! ## The rank-two bound on a Choi operator -/

section TwoBound

variable {W : Type*} [Fintype W]

/-- `β` bounds the `S(2)`-norm of `J` up to the factor two: the quadratic form of
`J` at the vectorization of a matrix of rank at most two is at most `2β` times
its squared Hilbert-Schmidt norm.

The rank-two hypothesis is unrolled, exactly as `FGPBound` unrolls "Schmidt rank
at most two": a matrix has rank at most two precisely when it is a sum of two
rank-one operators, so quantifying over the four vectors is the condition itself
and no separate notion of Schmidt rank is needed.

The least such `β` is `½‖J‖_{S(2)}`, a quantity of the map alone. -/
def ChoiTwoBound (J : Matrix (W × W) (W × W) ℂ) (β : ℝ) : Prop :=
  ∀ u₁ v₁ u₂ v₂ : EuclideanSpace ℂ W,
    (qform J (vec (rankOne u₁ v₁ + rankOne u₂ v₂))).re
      ≤ 2 * β * hsNormSq (rankOne u₁ v₁ + rankOne u₂ v₂)

/-- `β` is positively homogeneous: a rescaled map carries a rescaled constant, so
`Φ` and `β` always agree on the scale. -/
theorem choiTwoBound_smul {J : Matrix (W × W) (W × W) ℂ} {β t : ℝ} (ht : 0 ≤ t)
    (h : ChoiTwoBound J β) : ChoiTwoBound ((t : ℂ) • J) (t * β) := by
  intro u₁ v₁ u₂ v₂
  have hq := h u₁ v₁ u₂ v₂
  rw [qform_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  nlinarith [hq]

end TwoBound

/-! ## Lifting I

The amplification step of `lem:double-skew`, for an arbitrary Kraus family and
an arbitrary member of its span. -/

section LiftingOne

variable {W ι : Type*} [Fintype W] [Fintype ι]

/-- **Lifting I.**  For `K = ∑ₐ cₐ Aₐ` in the span of a Kraus family whose Choi
operator obeys `ChoiTwoBound _ β`, and any orthonormal pair `x ⊥ y`,

  `‖K x‖² + ‖K y‖² ≤ 2β ∑ₐ |cₐ|²`.

Writing `P` for the projection onto `span {x, y}` and `A = ‖K P‖₂²`, the chain is

  `A = ⟪K, K P⟫ = ∑ₐ conj(cₐ) ⟪Aₐ, K P⟫ ≤ ‖c‖ · ⟪vec(K P), J vec(K P)⟫^½
     ≤ ‖c‖ · (2β A)^½`,

after which one factor of `A` cancels.  The first equality is idempotence and
self-adjointness of `P`; the inequality is Cauchy-Schwarz on the Kraus index; the
last step is the rank-two bound applied to `K P`, whose two-term form
`|Kx⟩⟨x| + |Ky⟩⟨y|` is `mul_proj2`. -/
theorem norm_sq_pair_le_of_choiTwoBound {A : ι → Matrix W W ℂ} {β : ℝ} (hβ : 0 ≤ β)
    (hJ : ChoiTwoBound (choiOf A) β) (c : ι → ℂ)
    {x y : EuclideanSpace ℂ W} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : inner ℂ x y = (0 : ℂ)) :
    ‖mulVecE (∑ a, c a • A a) x‖ ^ 2 + ‖mulVecE (∑ a, c a • A a) y‖ ^ 2
      ≤ 2 * β * ∑ a, Complex.normSq (c a) := by
  set K : Matrix W W ℂ := ∑ a, c a • A a with hK
  set M : Matrix W W ℂ := K * proj2 x y with hM
  set N : ℝ := hsNormSq M with hN
  have hN0 : 0 ≤ N := hsNormSq_nonneg _
  -- the coefficient vector and the vector of overlaps, as Euclidean vectors
  set cv : EuclideanSpace ℂ ι := WithLp.toLp 2 c with hcv
  set zv : EuclideanSpace ℂ ι := WithLp.toLp 2 (fun a => hsInner (A a) M) with hzv
  have hcvn : ‖cv‖ ^ 2 = ∑ a, Complex.normSq (c a) := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    exact Finset.sum_congr rfl fun a _ => (Complex.normSq_eq_norm_sq _).symm
  have hzvn : ‖zv‖ ^ 2 = ∑ a, Complex.normSq (inner ℂ (vec (A a)) (vec M)) := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    exact Finset.sum_congr rfl fun a _ => by
      rw [← Complex.normSq_eq_norm_sq]
      exact congrArg Complex.normSq (hsInner_eq_inner _ _)
  -- `⟪c, z⟫ = ⟪K, K P⟫ = ‖K P‖₂²`
  have hpair : (inner ℂ cv zv : ℂ) = (N : ℂ) := by
    rw [← hsInner_mul_proj2 K hx hy hxy, hK, hsInner_sum_left]
    rw [PiLp.inner_apply]
    exact Finset.sum_congr rfl fun a _ => by
      rw [RCLike.inner_apply']
      exact (hsInner_smul_left _ _ _).symm
  have hcs : N ≤ ‖cv‖ * ‖zv‖ := by
    have h := norm_inner_le_norm (𝕜 := ℂ) cv zv
    rwa [hpair, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hN0] at h
  -- the rank-two bound, applied to `K P`
  have hrank2 : ‖zv‖ ^ 2 ≤ 2 * β * N := by
    rw [hzvn, ← re_qform_choiOf, hM, hN, hM]
    rw [mul_proj2]
    exact hJ _ _ _ _
  rw [← hsNormSq_mul_proj2 K hx hy hxy, ← hM, ← hN, ← hcvn]
  nlinarith [hcs, hrank2, hN0, norm_nonneg cv, norm_nonneg zv,
    mul_nonneg hβ (sq_nonneg ‖cv‖)]

end LiftingOne

end RankR
