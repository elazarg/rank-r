/-
The Choi operator of a Kraus family, and the amplification step of section 2.

A completely positive map `Φ` with Kraus family `{Aₐ}` has Choi operator

  `J(Φ) = ∑ₐ |vec Aₐ⟩⟨vec Aₐ|`,

the same operator for every Kraus family of `Φ`.  Its rank-two operator norm is
recorded as `β`:

  `ChoiTwoBound J β  ↔  ⟪z, J z⟫ ≤ 2β‖z‖²  for every `z` of Schmidt rank ≤ 2`,

so that `β = ½‖J(Φ)‖_{S(2)}`.  Since `J` is linear in `Φ`, so is `β`, and a map
and its constant always carry the same scale.

The same reading at every level `k` records `β_k = (1/k)‖J(Φ)‖_{S(k)}` as
`ChoiKBound J k β`, and `ChoiTwoBound` is the case `k = 2`
(`choiTwoBound_iff_choiKBound_two`).

Three hypotheses suffice for the amplification step of `lem:double-skew`: that
`K` lies in the span of the family, that `J(Φ)` obeys `ChoiKBound _ k β`, and
that `x` is an orthonormal `k`-tuple.  The compression `K P` onto the span of the
tuple pairs with `K` to `‖K P‖₂²`, expands along the Kraus index by
Cauchy-Schwarz, and has rank at most `k`, so the three combine into

  `∑ᵢ ‖K xᵢ‖² ≤ kβ ∑ₐ |cₐ|²`     (`norm_sq_le_of_choiKBound`),

of which the two-term form `‖K x‖² + ‖K y‖² ≤ 2β ∑ₐ |cₐ|²` is the case `k = 2`.
Only self-adjoint idempotence of the projection and the rank bound are used, so
the tuple length enters solely through the constant.

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

/-! ## The rank-`k` projection

`projK x` is the orthogonal projection onto the span of an orthonormal `k`-tuple.
Everything the amplification step asks of a compression is asked of a self-adjoint
idempotent of rank at most `k`, and no two-term structure is ever used, so the
four identities below are proved once, at arbitrary `k`; the rank-two projection
of `sec:double-skew` is the case `k = 2` and is derived from them. -/

section ProjectionK

variable {W : Type*} [Fintype W] {k : ℕ} {x : Fin k → EuclideanSpace ℂ W}

/-- The orthogonal projection onto the span of an orthonormal `k`-tuple. -/
noncomputable def projK {k : ℕ} (x : Fin k → EuclideanSpace ℂ W) : Matrix W W ℂ :=
  ∑ i, rankOne (x i) (x i)

omit [Fintype W] in
/-- A sum of rank-one projectors is self-adjoint. -/
theorem projK_conjTranspose : (projK x)ᴴ = projK x := by
  rw [projK, Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl fun i _ => rankOne_conjTranspose _ _

/-- Orthonormality of the tuple makes the projection idempotent: the cross terms
carry the vanishing overlaps and the diagonal terms reproduce the sum. -/
theorem projK_mul_self (hx : Orthonormal ℂ x) : projK x * projK x = projK x := by
  rw [projK, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_sum]
  have h : ∀ j : Fin k, rankOne (x i) (x i) * rankOne (x j) (x j)
      = if i = j then rankOne (x i) (x i) else 0 := fun j => by
    rw [rankOne_mul_rankOne, orthonormal_iff_ite.mp hx i j]
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl, if_pos rfl, one_smul]
    · rw [if_neg hij, if_neg hij, zero_smul]
  rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_ite_eq]
  simp

/-- `K P` is the `k`-term operator `∑ᵢ |K xᵢ⟩⟨xᵢ|`; this is the unrolling of
"rank at most `k`" that `ChoiKBound` quantifies over. -/
theorem mul_projK (K : Matrix W W ℂ) (x : Fin k → EuclideanSpace ℂ W) :
    K * projK x = ∑ i, rankOne (mulVecE K (x i)) (x i) := by
  rw [projK, Matrix.mul_sum]
  exact Finset.sum_congr rfl fun i _ => mul_rankOne _ _ _

/-- `‖K P‖₂²` is the action of `K` on the orthonormal tuple. -/
theorem hsNormSq_mul_projK (K : Matrix W W ℂ) (hx : Orthonormal ℂ x) :
    hsNormSq (K * projK x) = ∑ i, ‖mulVecE K (x i)‖ ^ 2 := by
  rw [mul_projK, ← Complex.ofReal_inj, ← hsInner_self, hsInner_sum_sum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : ∀ j : Fin k,
      hsInner (rankOne (mulVecE K (x i)) (x i)) (rankOne (mulVecE K (x j)) (x j))
        = if i = j then ((‖mulVecE K (x i)‖ ^ 2 : ℝ) : ℂ) else 0 := fun j => by
    rw [hsInner_rankOne, orthonormal_iff_ite.mp hx i j]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, if_pos rfl, map_one, mul_one, inner_self_eq_norm_sq_to_K]
      norm_cast
    · rw [if_neg hij, if_neg hij, map_zero, mul_zero]
  rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_ite_eq]
  simp

/-- `⟪K, K P⟫ = ‖K P‖₂²`, because `P` is a self-adjoint idempotent.  This is what
lets the compressed operator be tested against `K` itself. -/
theorem hsInner_mul_projK (K : Matrix W W ℂ) (hx : Orthonormal ℂ x) :
    hsInner K (K * projK x) = (hsNormSq (K * projK x) : ℂ) := by
  rw [← hsInner_self]
  have e1 : hsInner K (K * projK x) = (Kᴴ * K * projK x).trace := by
    rw [hsInner, Matrix.mul_assoc]
  have e2 : hsInner (K * projK x) (K * projK x) = (Kᴴ * K * projK x).trace := by
    rw [hsInner, Matrix.conjTranspose_mul, projK_conjTranspose,
      show projK x * Kᴴ * (K * projK x) = projK x * (Kᴴ * K * projK x) by
        simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm,
      show Kᴴ * K * projK x * projK x = Kᴴ * K * (projK x * projK x) by
        simp only [Matrix.mul_assoc],
      projK_mul_self hx]
  rw [e1, e2]

end ProjectionK

/-! ## The rank-two projection

`proj2 x y` is the orthogonal projection onto `span {x, y}` for an orthonormal
pair.  Compressing `K` by it produces a matrix of rank at most two whose squared
Hilbert-Schmidt norm is exactly the quantity to be bounded, and which pairs with
`K` to that same real number.

It is `projK` at `k = 2`, and every identity it needs is the `k = 2` case of one
proved above; only the two-term unrolling of the sum is new. -/

section Projection

variable {W : Type*} [Fintype W] {x y : EuclideanSpace ℂ W}

/-- The rank-two orthogonal projection onto `span {x, y}`. -/
noncomputable def proj2 (x y : EuclideanSpace ℂ W) : Matrix W W ℂ :=
  rankOne x x + rankOne y y

/-- An orthonormal pair, read as an orthonormal `Fin 2`-tuple. -/
theorem orthonormal_pair (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : inner ℂ x y = (0 : ℂ)) :
    Orthonormal ℂ ![x, y] := by
  have hyx : (inner ℂ y x : ℂ) = 0 := by rw [← inner_conj_symm, hxy, map_zero]
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [hxy, hyx, inner_self_eq_norm_sq_to_K, hx, hy]

omit [Fintype W] in
/-- `proj2` is `projK` at `k = 2`. -/
theorem proj2_eq_projK (x y : EuclideanSpace ℂ W) : proj2 x y = projK ![x, y] := by
  simp [proj2, projK, Fin.sum_univ_two]

omit [Fintype W] in
theorem proj2_conjTranspose : (proj2 x y)ᴴ = proj2 x y := by
  simp [proj2, Matrix.conjTranspose_add, rankOne_conjTranspose]

theorem proj2_mul_self (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : inner ℂ x y = (0 : ℂ)) :
    proj2 x y * proj2 x y = proj2 x y := by
  rw [proj2_eq_projK]
  exact projK_mul_self (orthonormal_pair hx hy hxy)

/-- `K P` is the two-term operator `|Kx⟩⟨x| + |Ky⟩⟨y|`; this is the unrolling of
"rank at most two" that `ChoiTwoBound` quantifies over. -/
theorem mul_proj2 (K : Matrix W W ℂ) (x y : EuclideanSpace ℂ W) :
    K * proj2 x y = rankOne (mulVecE K x) x + rankOne (mulVecE K y) y := by
  rw [proj2, Matrix.mul_add, mul_rankOne, mul_rankOne]

/-- `‖K P‖₂²` is the action of `K` on the orthonormal pair. -/
theorem hsNormSq_mul_proj2 (K : Matrix W W ℂ) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : inner ℂ x y = (0 : ℂ)) :
    hsNormSq (K * proj2 x y) = ‖mulVecE K x‖ ^ 2 + ‖mulVecE K y‖ ^ 2 := by
  rw [proj2_eq_projK, hsNormSq_mul_projK K (orthonormal_pair hx hy hxy)]
  simp [Fin.sum_univ_two]

/-- `⟪K, K P⟫ = ‖K P‖₂²`, because `P` is a self-adjoint idempotent.  This is what
lets the compressed operator be tested against `K` itself. -/
theorem hsInner_mul_proj2 (K : Matrix W W ℂ) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : inner ℂ x y = (0 : ℂ)) :
    hsInner K (K * proj2 x y) = (hsNormSq (K * proj2 x y) : ℂ) := by
  rw [proj2_eq_projK]
  exact hsInner_mul_projK K (orthonormal_pair hx hy hxy)

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
rank-one operators, so quantifying over the four vectors is the condition
itself.  `choiTwoBound_iff_pureSchmidtKBound_two` proves equivalence with the
direct `pureSchmidtRank` formulation.

The least such `β` is `½‖J‖_{S(2)}`, a quantity of the map alone.  For
`J = choiOf A` it is also `½ sup { s₁(K_c)² + s₂(K_c)² : ‖c‖ = 1 }` over the
Kraus span, which is the `k = 2` case of the `S(k)`-norm projection duality of
Johnston and Kribs, *A family of norms with applications in quantum information
theory*, J. Math. Phys. 51:082202 (2010); and `2β` is the threshold `a₂`
characterizing `2`-positivity of `a·Tr(·)I − Φ` in Młynik, Osaka and Marciniak,
*Characterization of k-positive maps*, Comm. Math. Phys. 406(3):62 (2025),
Thm. 3.2. -/
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

/-- `β` bounds the `S(k)`-norm of `J` up to the factor `k`: the quadratic form of
`J` at the vectorization of a matrix of rank at most `k` is at most `kβ` times its
squared Hilbert-Schmidt norm.

The rank-`k` hypothesis is unrolled the same way `ChoiTwoBound` unrolls rank two:
a matrix has rank at most `k` precisely when it is a sum of `k` rank-one
operators, so quantifying over the two `k`-tuples of vectors is the condition
itself.

The least such `β` is `β_k = (1/k)‖J‖_{S(k)}`, the level-`k` Choi constant; the
normalization by `k` is what makes `β_k` decrease as `k` grows and keeps `β_2`
equal to the constant of pair amplification. -/
def ChoiKBound (J : Matrix (W × W) (W × W) ℂ) (k : ℕ) (β : ℝ) : Prop :=
  ∀ u v : Fin k → EuclideanSpace ℂ W,
    (qform J (vec (∑ i, rankOne (u i) (v i)))).re
      ≤ k * β * hsNormSq (∑ i, rankOne (u i) (v i))

/-- The level-`k` bound is positively homogeneous in the Choi operator. -/
theorem choiKBound_smul {J : Matrix (W × W) (W × W) ℂ}
    {k : ℕ} {β t : ℝ} (ht : 0 ≤ t)
    (h : ChoiKBound J k β) :
    ChoiKBound ((t : ℂ) • J) k (t * β) := by
  intro u v
  have hq := h u v
  rw [qform_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  nlinarith [hq, Nat.cast_nonneg (α := ℝ) k,
    hsNormSq_nonneg (∑ i, rankOne (u i) (v i))]

/-- A level-`k` Choi constant is attained when a nonzero `k`-term matrix
meets its defining quadratic-form inequality with equality. -/
def ChoiKAttained (J : Matrix (W × W) (W × W) ℂ) (k : ℕ) (β : ℝ) : Prop :=
  ∃ u v : Fin k → EuclideanSpace ℂ W,
    (∑ i, rankOne (u i) (v i)) ≠ 0 ∧
      (qform J (vec (∑ i, rankOne (u i) (v i)))).re
        = k * β * hsNormSq (∑ i, rankOne (u i) (v i))

/-- An attained positive-level constant lies below every valid constant. -/
theorem le_of_choiKAttained {J : Matrix (W × W) (W × W) ℂ}
    {k : ℕ} {β β' : ℝ} (hk : 0 < k)
    (ha : ChoiKAttained J k β) (hb : ChoiKBound J k β') :
    β ≤ β' := by
  obtain ⟨u, v, hne, heq⟩ := ha
  have hpos : 0 < hsNormSq (∑ i, rankOne (u i) (v i)) :=
    hsNormSq_pos hne
  have hle := hb u v
  rw [heq] at hle
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hfactor :
      0 < (k : ℝ) * hsNormSq (∑ i, rankOne (u i) (v i)) :=
    mul_pos hkR hpos
  have hle' :
      ((k : ℝ) * hsNormSq (∑ i, rankOne (u i) (v i))) * β
        ≤ ((k : ℝ) * hsNormSq (∑ i, rankOne (u i) (v i))) * β' := by
    calc
      ((k : ℝ) * hsNormSq (∑ i, rankOne (u i) (v i))) * β =
          (k : ℝ) * β * hsNormSq (∑ i, rankOne (u i) (v i)) := by ring
      _ ≤ (k : ℝ) * β' * hsNormSq (∑ i, rankOne (u i) (v i)) := hle
      _ = ((k : ℝ) * hsNormSq (∑ i, rankOne (u i) (v i))) * β' := by ring
  exact le_of_mul_le_mul_left hle' hfactor

/-- Attainment scales with the Choi operator. -/
theorem choiKAttained_smul {J : Matrix (W × W) (W × W) ℂ}
    {k : ℕ} {β t : ℝ} (h : ChoiKAttained J k β) :
    ChoiKAttained ((t : ℂ) • J) k (t * β) := by
  obtain ⟨u, v, hne, heq⟩ := h
  refine ⟨u, v, hne, ?_⟩
  rw [qform_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, heq]
  ring

/-- A valid level-`k` bound remains valid when its coefficient is increased. -/
theorem choiKBound_mono {J : Matrix (W × W) (W × W) ℂ}
    {k : ℕ} {β β' : ℝ} (h : ChoiKBound J k β) (hβ : β ≤ β') :
    ChoiKBound J k β' := by
  intro u v
  have hq := h u v
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hn0 : 0 ≤ hsNormSq (∑ i, rankOne (u i) (v i)) :=
    hsNormSq_nonneg _
  have hfactor :
      0 ≤ (k : ℝ) * hsNormSq (∑ i, rankOne (u i) (v i)) :=
    mul_nonneg hk0 hn0
  apply hq.trans
  have hmul := mul_le_mul_of_nonneg_left hβ hfactor
  calc
    (k : ℝ) * β * hsNormSq (∑ i, rankOne (u i) (v i)) =
        ((k : ℝ) * hsNormSq (∑ i, rankOne (u i) (v i))) * β := by ring
    _ ≤ ((k : ℝ) * hsNormSq (∑ i, rankOne (u i) (v i))) * β' := hmul
    _ = (k : ℝ) * β' * hsNormSq (∑ i, rankOne (u i) (v i)) := by ring

/-- Any nonzero rank-at-most-`k` matrix attaining the homogeneous
quadratic-form equality supplies a `ChoiKAttained` witness. -/
theorem choiKAttained_of_matrix {J : Matrix (W × W) (W × W) ℂ}
    {k : ℕ} {β : ℝ} {M : Matrix W W ℂ}
    [DecidableEq W]
    (hrank : M.rank ≤ k) (hne : M ≠ 0)
    (heq : (qform J (vec M)).re = k * β * hsNormSq M) :
    ChoiKAttained J k β := by
  obtain ⟨u, v, hM⟩ := (rank_le_iff_exists_sum_rankOne M).mp hrank
  subst M
  exact ⟨u, v, hne, heq⟩

/-- The same level-`k` Choi bound stated directly for bipartite vectors of
pure Schmidt rank at most `k`.  Its equivalence with `ChoiKBound` is proved in
`Equivalence.lean`. -/
def PureSchmidtKBound
    (J : Matrix (W × W) (W × W) ℂ) (k : ℕ) (β : ℝ) : Prop :=
  ∀ z : EuclideanSpace ℂ (W × W), pureSchmidtRank z ≤ k →
    (qform J z).re ≤ k * β * ‖z‖ ^ 2

/-- **The rank-two bound is the level-two bound.**  A sum of two rank-one
operators is a `Fin 2`-indexed sum of rank-one operators, and `k = 2` makes the
two constants agree. -/
theorem choiTwoBound_iff_choiKBound_two {J : Matrix (W × W) (W × W) ℂ} {β : ℝ} :
    ChoiTwoBound J β ↔ ChoiKBound J 2 β := by
  constructor
  · intro h u v
    have hu := h (u 0) (v 0) (u 1) (v 1)
    rw [Fin.sum_univ_two]
    push_cast
    exact hu
  · intro h u₁ v₁ u₂ v₂
    have hu := h ![u₁, u₂] ![v₁, v₂]
    rw [Fin.sum_univ_two] at hu
    push_cast at hu
    simpa using hu

end TwoBound

/-! ## Lifting I

The amplification step of `lem:double-skew`, for an arbitrary Kraus family and
an arbitrary member of its span. -/

section LiftingOne

variable {W ι : Type*} [Fintype W] [Fintype ι]

/-- **Lifting I, at level `k`.**  For `K = ∑ₐ cₐ Aₐ` in the span of a Kraus family
whose Choi operator obeys `ChoiKBound _ k β`, and any orthonormal `k`-tuple `x`,

  `∑ᵢ ‖K xᵢ‖² ≤ kβ ∑ₐ |cₐ|²`.

Writing `P` for the projection onto the span of the tuple and `A = ‖K P‖₂²`, the
chain is

  `A = ⟪K, K P⟫ = ∑ₐ conj(cₐ) ⟪Aₐ, K P⟫ ≤ ‖c‖ · ⟪vec(K P), J vec(K P)⟫^½
     ≤ ‖c‖ · (kβ A)^½`,

after which one factor of `A` cancels.  The first equality is idempotence and
self-adjointness of `P`; the inequality is Cauchy-Schwarz on the Kraus index; the
last step is the rank-`k` bound applied to `K P`, whose `k`-term form
`∑ᵢ |K xᵢ⟩⟨xᵢ|` is `mul_projK`.

Read through `vec`, this is `‖S‖² ≤ ‖S S*‖` for the synthesis operator
`S : c ↦ ∑ₐ cₐ Aₐ` in the `S(k)`-norm, the elementary half of the Johnston-Kribs
duality; that a rank-`k` compression suffices to test an orthonormal `k`-tuple is
Takasaki and Tomiyama, *On the geometry of positive maps in matrix algebras*,
Math. Z. 184:101--108 (1983), Prop. 1.1. -/
theorem norm_sq_le_of_choiKBound {A : ι → Matrix W W ℂ} {β : ℝ} (hβ : 0 ≤ β) {k : ℕ}
    (hJ : ChoiKBound (choiOf A) k β) (c : ι → ℂ)
    {x : Fin k → EuclideanSpace ℂ W} (hx : Orthonormal ℂ x) :
    ∑ i, ‖mulVecE (∑ a, c a • A a) (x i)‖ ^ 2
      ≤ k * β * ∑ a, Complex.normSq (c a) := by
  set K : Matrix W W ℂ := ∑ a, c a • A a with hK
  set M : Matrix W W ℂ := K * projK x with hM
  set N : ℝ := hsNormSq M with hN
  have hN0 : 0 ≤ N := hsNormSq_nonneg _
  -- the coefficient vector and the vector of overlaps, as Euclidean vectors
  set cv : EuclideanSpace ℂ ι := WithLp.toLp 2 c with hcv
  set zv : EuclideanSpace ℂ ι := WithLp.toLp 2 (fun a => hsInner (A a) M) with hzv
  have hcvn : ‖cv‖ ^ 2 = ∑ a, Complex.normSq (c a) := norm_sq_eq_sum_normSq _
  have hzvn : ‖zv‖ ^ 2 = ∑ a, Complex.normSq (inner ℂ (vec (A a)) (vec M)) := by
    rw [norm_sq_eq_sum_normSq]
    exact Finset.sum_congr rfl fun a _ => congrArg Complex.normSq (hsInner_eq_inner _ _)
  -- `⟪c, z⟫ = ⟪K, K P⟫ = ‖K P‖₂²`
  have hpair : (inner ℂ cv zv : ℂ) = (N : ℂ) := by
    rw [← hsInner_mul_projK K hx, hK, hsInner_sum_left, PiLp.inner_apply]
    exact Finset.sum_congr rfl fun a _ => by
      rw [RCLike.inner_apply']
      exact (hsInner_smul_left _ _ _).symm
  have hcs : N ≤ ‖cv‖ * ‖zv‖ := by
    have h := norm_inner_le_norm (𝕜 := ℂ) cv zv
    rwa [hpair, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hN0] at h
  -- the rank-`k` bound, applied to `K P`
  have hrankk : ‖zv‖ ^ 2 ≤ k * β * N := by
    rw [hzvn, ← re_qform_choiOf, hM, hN, hM, mul_projK]
    exact hJ (fun i => mulVecE K (x i)) x
  rw [← hsNormSq_mul_projK K hx, ← hM, ← hN, ← hcvn]
  nlinarith [hcs, hrankk, hN0, norm_nonneg cv, norm_nonneg zv,
    mul_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hβ) (sq_nonneg ‖cv‖)]

/-- **Lifting I.**  The level-two case, in the two-term form the amplification
step of `lem:double-skew` consumes: for an orthonormal pair `x ⊥ y`,

  `‖K x‖² + ‖K y‖² ≤ 2β ∑ₐ |cₐ|²`. -/
theorem norm_sq_pair_le_of_choiTwoBound {A : ι → Matrix W W ℂ} {β : ℝ} (hβ : 0 ≤ β)
    (hJ : ChoiTwoBound (choiOf A) β) (c : ι → ℂ)
    {x y : EuclideanSpace ℂ W} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : inner ℂ x y = (0 : ℂ)) :
    ‖mulVecE (∑ a, c a • A a) x‖ ^ 2 + ‖mulVecE (∑ a, c a • A a) y‖ ^ 2
      ≤ 2 * β * ∑ a, Complex.normSq (c a) := by
  have h := norm_sq_le_of_choiKBound hβ (choiTwoBound_iff_choiKBound_two.mp hJ) c
    (orthonormal_pair hx hy hxy)
  rw [Fin.sum_univ_two] at h
  push_cast at h
  simpa using h

end LiftingOne

end RankR
