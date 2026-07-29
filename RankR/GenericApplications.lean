/-
Generic finite-coordinate consequences of block positivity.

The main development usually uses the square bipartition `W : W`.  The
positive-map semidefinite cut in `app:generic` has an arbitrary ancilla, so this
file first gives the same pure-state decomposition definition for an `A : B`
bipartition.  It then proves directly that a Choi operator which is
`r`-block-positive maps every such Schmidt-number-`r` positive operator to a
positive semidefinite matrix, even when the ancilla has more than `r`
coordinates.
-/
import RankR.TraceSeparation
import RankR.MapPos

namespace RankR

open Matrix Finset ComplexConjugate
open scoped ComplexOrder Kronecker MatrixOrder

/-! ## Schmidt number across a rectangular bipartition -/

section SchmidtNumberBetween

variable {A B : Type*} [Fintype A] [Fintype B]

/-- Block positivity across a possibly rectangular coordinate bipartition. -/
def IsBlockPositiveBetween (r : ℕ)
    (M : Matrix (A × B) (A × B) ℂ) : Prop :=
  ∀ C : Matrix A B ℂ, C.rank ≤ r → 0 ≤ (qform M (vec C)).re

/-- Mixed-state Schmidt number at most `r` across the coordinate bipartition
`A : B`.  The coefficient matrix of each pure vector is rectangular. -/
def SchmidtNumberLEBetween (r : ℕ)
    (ρ : Matrix (A × B) (A × B) ℂ) : Prop :=
  ∃ n : ℕ, ∃ C : Fin n → Matrix A B ℂ,
    (∀ i, (C i).rank ≤ r) ∧
      ρ = ∑ i, rankOne (vec (C i)) (vec (C i))

/-- The square-bipartition definition used by the trace-separation
development is the corresponding instance of `SchmidtNumberLEBetween`. -/
theorem schmidtNumberLEBetween_self_iff {r : ℕ}
    {ρ : Matrix (B × B) (B × B) ℂ} :
    SchmidtNumberLEBetween (A := B) (B := B) r ρ ↔ SchmidtNumberLE r ρ :=
  Iff.rfl

/-- The original square block-positivity predicate is the corresponding
instance of `IsBlockPositiveBetween`. -/
theorem isBlockPositiveBetween_self_iff {r : ℕ}
    {M : Matrix (B × B) (B × B) ℂ} :
    IsBlockPositiveBetween (A := B) (B := B) r M ↔ IsBlockPositive r M :=
  Iff.rfl

/-- Rectangular block positivity extends to the corresponding mixed-state
Schmidt-number cone. -/
theorem re_hsInner_nonneg_of_schmidtNumberLEBetween {r : ℕ}
    {M ρ : Matrix (A × B) (A × B) ℂ}
    (hM : IsBlockPositiveBetween r M)
    (hρ : SchmidtNumberLEBetween r ρ) :
    0 ≤ (hsInner M ρ).re := by
  obtain ⟨n, C, hCrank, rfl⟩ := hρ
  rw [hsInner_sum_right, Complex.re_sum]
  exact Finset.sum_nonneg fun i _ => by
    rw [re_hsInner_rankOne]
    exact hM (C i) (hCrank i)

/-- The Hermitian trace/inner-product identity for an arbitrary finite
coordinate type. -/
theorem trace_mul_eq_hsInner_of_isHermitian_finite
    {X : Type*} [Fintype X] {M ρ : Matrix X X ℂ}
    (hM : M.IsHermitian) :
    (M * ρ).trace = hsInner M ρ := by
  rw [hsInner, hM.eq]

/-- A rectangular block-positive Hermitian witness has nonnegative trace
pairing with every operator in the matching Schmidt-number cone. -/
theorem trace_mul_nonneg_of_schmidtNumberLEBetween {r : ℕ}
    {M ρ : Matrix (A × B) (A × B) ℂ}
    (hHerm : M.IsHermitian) (hM : IsBlockPositiveBetween r M)
    (hρ : SchmidtNumberLEBetween r ρ) :
    0 ≤ ((M * ρ).trace).re := by
  rw [trace_mul_eq_hsInner_of_isHermitian_finite hHerm]
  exact re_hsInner_nonneg_of_schmidtNumberLEBetween hM hρ

end SchmidtNumberBetween

/-! ## Extending an `r`-positive map to arbitrary Schmidt-rank-`r` inputs -/

section PositiveMapCut

variable {A W : Type*} [Fintype A] [Fintype W]
  [DecidableEq A] [DecidableEq W]

/-- Contracting a vectorized rank-at-most-`r` coefficient matrix against an
arbitrary output vector still produces a Choi test matrix of rank at most
`r`.  The proof factors the coefficient matrix through `Fin r`; this avoids
any restriction on the size of the ambient ancilla `A`. -/
theorem rank_choiContraction_vec_le {r : ℕ} (C : Matrix A W ℂ)
    (hrank : C.rank ≤ r) (y : EuclideanSpace ℂ (A × W)) :
    (choiContraction (vec C) y).rank ≤ r := by
  have hcard : C.rank ≤ Fintype.card (Fin r) := by
    simpa using hrank
  obtain ⟨X, Y, hXY⟩ :=
    (rank_le_card_iff_exists_mul (A := Fin r) C).mp hcard
  let Z : Matrix W A ℂ := Matrix.of fun o a => y (a, o)
  have hfac :
      choiContraction (vec C) y =
        (Z * X.map (starRingEnd ℂ)) * Y.map (starRingEnd ℂ) := by
    rw [← hXY]
    ext o i
    simp only [choiContraction, Matrix.of_apply, vec_apply, Matrix.mul_apply,
      Matrix.map_apply, map_sum, map_mul, Z]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun q _ => by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun a _ => by ring
  rw [hfac]
  refine (Matrix.rank_mul_le_left _ _).trans ?_
  simpa using Matrix.rank_le_card_width
    (Z * X.map (starRingEnd ℂ))

/-- An `r`-block-positive Choi operator sends a pure input of Schmidt rank at
most `r` to a positive semidefinite output, for an ancilla of arbitrary finite
dimension. -/
theorem mapAmplification_mapOfChoi_rankOne_vec_posSemidef
    {r : ℕ} {M : Matrix (W × W) (W × W) ℂ}
    (hM : M.IsHermitian) (hblock : IsBlockPositive r M)
    (C : Matrix A W ℂ) (hrank : C.rank ≤ r) :
    (mapAmplification (A := A) (mapOfChoi M)
      (rankOne (vec C) (vec C))).PosSemidef := by
  have hxHerm : (rankOne (vec C) (vec C)).IsHermitian := by
    simpa [Matrix.IsHermitian] using rankOne_conjTranspose (vec C) (vec C)
  have houtHerm :=
    mapAmplification_mapOfChoi_isHermitian (A := A) hM hxHerm
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg houtHerm ?_
  intro y
  rw [show star y ⬝ᵥ
      (mapAmplification (A := A) (mapOfChoi M)
        (rankOne (vec C) (vec C)) *ᵥ y) =
      qform (mapAmplification (A := A) (mapOfChoi M)
        (rankOne (vec C) (vec C))) (WithLp.toLp 2 y) by
      simp [qform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]]
  apply Complex.nonneg_iff.mpr
  constructor
  · rw [qform_mapAmplification_mapOfChoi_rankOne]
    exact hblock (choiContraction (vec C) (WithLp.toLp 2 y))
      (rank_choiContraction_vec_le C hrank (WithLp.toLp 2 y))
  · have him := houtHerm.im_star_dotProduct_mulVec_self y
    rw [show star y ⬝ᵥ
        (mapAmplification (A := A) (mapOfChoi M)
          (rankOne (vec C) (vec C)) *ᵥ y) =
        qform (mapAmplification (A := A) (mapOfChoi M)
          (rankOne (vec C) (vec C))) (WithLp.toLp 2 y) by
        simp [qform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]] at him
    exact him.symm

/-- A block-positive Choi operator gives the positive-map semidefinite cut on
every positive operator of Schmidt number at most `r`, with no bound on the
ambient ancilla dimension. -/
theorem mapAmplification_posSemidef_of_schmidtNumberLEBetween
    {r : ℕ} {M : Matrix (W × W) (W × W) ℂ}
    (hM : M.IsHermitian) (hblock : IsBlockPositive r M)
    {ρ : Matrix (A × W) (A × W) ℂ}
    (hρ : SchmidtNumberLEBetween r ρ) :
    (mapAmplification (A := A) (mapOfChoi M) ρ).PosSemidef := by
  obtain ⟨n, C, hCrank, rfl⟩ := hρ
  change
    (mapAmplificationLinear (A := A) (mapOfChoiLinear M)
      (∑ i, rankOne (vec (C i)) (vec (C i)))).PosSemidef
  rw [map_sum]
  exact (Finset.sum_nonneg fun i _ =>
    (mapAmplification_mapOfChoi_rankOne_vec_posSemidef
      hM hblock (C i) (hCrank i)).nonneg).posSemidef

end PositiveMapCut

/-! ## The reduction-product semidefinite cut -/

section ReductionCut

variable {A T : Type*} [Fintype A] [Fintype T]
  [DecidableEq A] [DecidableEq T]

/-- The asymmetric positive-map cut from `cor:positive-map-cut`, in finite
coordinates and for an arbitrary finite ancilla. -/
theorem productReduction_schmidtNumberLE_cut
    {r : ℕ} (hr : 0 < r) (hTtwo : 2 ≤ Fintype.card T)
    {a b : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (hab : max a b ≤ 1 / (min r (Fintype.card T) : ℝ))
    {ρ : Matrix (A × (T × T)) (A × (T × T)) ℂ}
    (hρ : SchmidtNumberLEBetween r ρ) :
    (mapAmplification (A := A)
      (productReductionMapLinear (U := T) (V := T) a b) ρ).PosSemidef := by
  have hblock :
      IsBlockPositive r
        (productReductionChoi (U := T) (V := T) a b) :=
    (isBlockPositive_productReductionChoi_iff_max_le_inv_min
      hr hTtwo ha0 hb0).2 hab
  change
    (mapAmplification (A := A)
      (mapOfChoi (productReductionChoi (U := T) (V := T) a b)) ρ).PosSemidef
  exact mapAmplification_posSemidef_of_schmidtNumberLEBetween
    (productReductionChoi_isHermitian a b) hblock hρ

/-- The symmetric specialization
`Λ_r = R_{-1/min(r,d)} ⊗ R_{-1/min(r,d)}`. -/
theorem productReduction_self_schmidtNumberLE_cut
    {r : ℕ} (hr : 0 < r) (hTtwo : 2 ≤ Fintype.card T)
    {ρ : Matrix (A × (T × T)) (A × (T × T)) ℂ}
    (hρ : SchmidtNumberLEBetween r ρ) :
    let s := min r (Fintype.card T)
    (mapAmplification (A := A)
      (productReductionMapLinear (U := T) (V := T)
        (1 / (s : ℝ)) (1 / (s : ℝ))) ρ).PosSemidef := by
  dsimp only
  have hTpos : 0 < Fintype.card T := by omega
  have hspos : 0 < min r (Fintype.card T) := lt_min hr hTpos
  apply productReduction_schmidtNumberLE_cut hr hTtwo
  · positivity
  · positivity
  · simp
  · exact hρ

end ReductionCut

/-! ## Local Kraus pullbacks and aggregation -/

section RectangularAction

variable {I O : Type*} [Fintype I] [Fintype O]

/-- Matrix-vector multiplication between two different finite coordinate
types. -/
def mulVecRect (K : Matrix O I ℂ) (x : EuclideanSpace ℂ I) :
    EuclideanSpace ℂ O :=
  WithLp.toLp 2 (K.mulVec (WithLp.ofLp x))

omit [Fintype O] in
@[simp] theorem mulVecRect_apply (K : Matrix O I ℂ)
    (x : EuclideanSpace ℂ I) (o : O) :
    mulVecRect K x o = ∑ i, K o i * x i := rfl

/-- Pulling a quadratic form back through a rectangular matrix. -/
theorem qform_conj_rect (K : Matrix O I ℂ) (Y : Matrix O O ℂ)
    (x : EuclideanSpace ℂ I) :
    qform (Kᴴ * Y * K) x = qform Y (mulVecRect K x) := by
  have hL : qform (Kᴴ * Y * K) x =
      ∑ p, ∑ q, ∑ u, ∑ v,
        conj (x p) * conj (K u p) * Y u v * K v q * x q := by
    simp only [qform]
    refine Finset.sum_congr rfl fun p _ =>
      Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_comm]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def,
      Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ =>
      Finset.sum_congr rfl fun u _ => by ring
  have hR : qform Y (mulVecRect K x) =
      ∑ u, ∑ v, ∑ p, ∑ q,
        conj (x p) * conj (K u p) * Y u v * K v q * x q := by
    simp only [qform]
    refine Finset.sum_congr rfl fun u _ =>
      Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_comm]
    simp only [mulVecRect_apply, map_sum, map_mul,
      Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ =>
      Finset.sum_congr rfl fun q _ => by ring
  rw [hL, hR]
  exact (sum4_swap fun p q u v =>
    conj (x p) * conj (K u p) * Y u v * K v q * x q).symm

end RectangularAction

section LocalKraus

variable {A B C D : Type*}
  [Fintype A] [Fintype B] [Fintype C] [Fintype D]

/-- The coefficient matrix obtained by applying local operators on the two
sides of a pure bipartite vector. -/
noncomputable def localCoeff
    (L : Matrix C A ℂ) (R : Matrix D B ℂ) (X : Matrix A B ℂ) :
    Matrix C D ℂ :=
  L * X * Rᵀ

/-- The product-space matrix of the local operator `L ⊗ R`. -/
noncomputable def localKrausMatrix
    (L : Matrix C A ℂ) (R : Matrix D B ℂ) :
    Matrix (C × D) (A × B) ℂ :=
  L ⊗ₖ R

omit [Fintype C] [Fintype D] in
/-- The local Kronecker action agrees with the coefficient-matrix action. -/
theorem mulVecRect_localKrausMatrix_vec
    (L : Matrix C A ℂ) (R : Matrix D B ℂ) (X : Matrix A B ℂ) :
    mulVecRect (localKrausMatrix L R) (vec X) = vec (localCoeff L R X) := by
  ext ⟨c, d⟩
  simp only [mulVecRect_apply, localKrausMatrix, Matrix.kroneckerMap_apply,
    vec_apply, Fintype.sum_prod_type, localCoeff, Matrix.mul_apply,
    Matrix.transpose_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by ring

omit [Fintype C] in
/-- Local left and right multiplication cannot increase the coefficient
matrix rank. -/
theorem rank_localCoeff_le (L : Matrix C A ℂ) (R : Matrix D B ℂ)
    (X : Matrix A B ℂ) :
    (localCoeff L R X).rank ≤ X.rank := by
  exact (Matrix.rank_mul_le_left (L * X) Rᵀ).trans
    (Matrix.rank_mul_le_right L X)

variable {P Q : Type*} [Fintype P] [Fintype Q]

/-- Pull a witness back through all pairs of two local Kraus families. -/
noncomputable def localKrausPullback
    (L : P → Matrix C A ℂ) (R : Q → Matrix D B ℂ)
    (W : Matrix (C × D) (C × D) ℂ) :
    Matrix (A × B) (A × B) ℂ :=
  ∑ i, ∑ j,
    (localKrausMatrix (L i) (R j))ᴴ * W *
      localKrausMatrix (L i) (R j)

/-- Kraus completeness, equivalently trace preservation of the associated
finite Kraus map. -/
def IsTracePreservingKraus [DecidableEq A]
    (L : P → Matrix C A ℂ) : Prop :=
  ∑ i, (L i)ᴴ * L i = 1

/-- The quadratic form of a local Kraus pullback is the sum of the output
witness forms on all locally transformed coefficient matrices. -/
theorem qform_localKrausPullback
    (L : P → Matrix C A ℂ) (R : Q → Matrix D B ℂ)
    (W : Matrix (C × D) (C × D) ℂ) (X : Matrix A B ℂ) :
    qform (localKrausPullback L R W) (vec X) =
      ∑ i, ∑ j, qform W (vec (localCoeff (L i) (R j) X)) := by
  rw [localKrausPullback, qform_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [qform_sum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [qform_conj_rect, mulVecRect_localKrausMatrix_vec]

/-- Local Kraus pullback preserves block positivity.  Trace preservation is
not needed for this conclusion. -/
theorem localKrausPullback_isBlockPositiveBetween {r : ℕ}
    (L : P → Matrix C A ℂ) (R : Q → Matrix D B ℂ)
    {W : Matrix (C × D) (C × D) ℂ}
    (hW : IsBlockPositiveBetween r W) :
    IsBlockPositiveBetween r (localKrausPullback L R W) := by
  intro X hrank
  rw [qform_localKrausPullback, Complex.re_sum]
  exact Finset.sum_nonneg fun i _ => by
    rw [Complex.re_sum]
    exact Finset.sum_nonneg fun j _ =>
      hW (localCoeff (L i) (R j) X)
        ((rank_localCoeff_le (L i) (R j) X).trans hrank)

omit [Fintype A] [Fintype B] in
/-- Pullback through local Kraus families preserves Hermiticity. -/
theorem localKrausPullback_isHermitian
    (L : P → Matrix C A ℂ) (R : Q → Matrix D B ℂ)
    {W : Matrix (C × D) (C × D) ℂ} (hW : W.IsHermitian) :
    (localKrausPullback L R W).IsHermitian := by
  rw [Matrix.IsHermitian, localKrausPullback, Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun j _ => by
      simp [Matrix.conjTranspose_mul, hW.eq, Matrix.mul_assoc]

/-- Pullback through local Kraus families preserves positive
semidefiniteness. -/
theorem localKrausPullback_posSemidef
    (L : P → Matrix C A ℂ) (R : Q → Matrix D B ℂ)
    {W : Matrix (C × D) (C × D) ℂ} (hW : W.PosSemidef) :
    (localKrausPullback L R W).PosSemidef := by
  rw [localKrausPullback]
  exact (Finset.sum_nonneg fun i _ =>
    (Finset.sum_nonneg fun j _ =>
      (hW.conjTranspose_mul_mul_same
        (localKrausMatrix (L i) (R j))).nonneg).posSemidef.nonneg).posSemidef

omit [Fintype A] [Fintype B] in
/-- Local Kraus pullback is additive. -/
theorem localKrausPullback_add
    (L : P → Matrix C A ℂ) (R : Q → Matrix D B ℂ)
    (W Z : Matrix (C × D) (C × D) ℂ) :
    localKrausPullback L R (W + Z) =
      localKrausPullback L R W + localKrausPullback L R Z := by
  simp only [localKrausPullback, Matrix.mul_add, Matrix.add_mul,
    Finset.sum_add_distrib]

omit [Fintype A] [Fintype B] in
/-- Local Kraus pullback commutes with scalar multiplication. -/
theorem localKrausPullback_smul
    (L : P → Matrix C A ℂ) (R : Q → Matrix D B ℂ)
    (c : ℂ) (W : Matrix (C × D) (C × D) ℂ) :
    localKrausPullback L R (c • W) =
      c • localKrausPullback L R W := by
  simp only [localKrausPullback, Matrix.mul_smul, Matrix.smul_mul,
    Finset.smul_sum]

omit [Fintype A] [Fintype B] in
/-- Local Kraus pullback commutes with subtraction. -/
theorem localKrausPullback_sub
    (L : P → Matrix C A ℂ) (R : Q → Matrix D B ℂ)
    (W Z : Matrix (C × D) (C × D) ℂ) :
    localKrausPullback L R (W - Z) =
      localKrausPullback L R W - localKrausPullback L R Z := by
  simp only [localKrausPullback, Matrix.mul_sub, Matrix.sub_mul,
    Finset.sum_sub_distrib]

omit [Fintype A] [Fintype B] in
/-- The adjoint of a product of trace-preserving local Kraus maps is unital. -/
theorem localKrausPullback_one
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    (L : P → Matrix C A ℂ) (R : Q → Matrix D B ℂ)
    (hL : IsTracePreservingKraus L)
    (hR : IsTracePreservingKraus R) :
    localKrausPullback L R
        (1 : Matrix (C × D) (C × D) ℂ) =
      (1 : Matrix (A × B) (A × B) ℂ) := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  have hLa := congrArg (fun M : Matrix A A ℂ => M a a') hL
  have hRb := congrArg (fun M : Matrix B B ℂ => M b b') hR
  simp only [Matrix.sum_apply, Matrix.one_apply] at hLa hRb
  simp only [localKrausPullback, Matrix.sum_apply, Matrix.mul_one,
    localKrausMatrix, Matrix.conjTranspose_kronecker, Matrix.one_apply]
  simp_rw [← Matrix.mul_kronecker_mul, Matrix.kroneckerMap_apply]
  calc
    (∑ i, ∑ j, ((L i)ᴴ * L i) a a' * ((R j)ᴴ * R j) b b') =
        (∑ i, ((L i)ᴴ * L i) a a') *
          (∑ j, ((R j)ᴴ * R j) b b') := by
            rw [Finset.sum_mul_sum]
    _ = (if a = a' then 1 else 0) * (if b = b' then 1 else 0) := by
      rw [hLa, hRb]
    _ = if (a, b) = (a', b') then 1 else 0 := by
      by_cases ha : a = a' <;> by_cases hb : b = b' <;> simp [ha, hb]

omit [Fintype A] [Fintype B] in
/-- Under Kraus completeness, shifting the output witness shifts its pullback
by the same scalar identity. -/
theorem localKrausPullback_sub_smul_one
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    (L : P → Matrix C A ℂ) (R : Q → Matrix D B ℂ)
    (hL : IsTracePreservingKraus L)
    (hR : IsTracePreservingKraus R)
    (W : Matrix (C × D) (C × D) ℂ) (c : ℂ) :
    localKrausPullback L R
        (W - c • (1 : Matrix (C × D) (C × D) ℂ)) =
      localKrausPullback L R W -
        c • (1 : Matrix (A × B) (A × B) ℂ) := by
  rw [localKrausPullback_sub, localKrausPullback_smul,
    localKrausPullback_one L R hL hR]

end LocalKraus

section Aggregation

variable {A B C D E P Q : Type*}
  [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [Fintype E] [Fintype P] [Fintype Q]

/-- A weighted sum of witnesses pulled back through local Kraus families.
The output and Kraus index types are common finite coordinate spaces; varying
finite outputs can be embedded into a common direct-sum coordinate type. -/
noncomputable def aggregateLocalWitness
    (weights : E → ℝ)
    (L : E → P → Matrix C A ℂ) (R : E → Q → Matrix D B ℂ)
    (W : E → Matrix (C × D) (C × D) ℂ) :
    Matrix (A × B) (A × B) ℂ :=
  ∑ e, (weights e : ℂ) • localKrausPullback (L e) (R e) (W e)

/-- Nonnegative weighted aggregation preserves block positivity. -/
theorem aggregateLocalWitness_isBlockPositiveBetween {r : ℕ}
    {weights : E → ℝ} (hweights : ∀ e, 0 ≤ weights e)
    (L : E → P → Matrix C A ℂ) (R : E → Q → Matrix D B ℂ)
    {W : E → Matrix (C × D) (C × D) ℂ}
    (hW : ∀ e, IsBlockPositiveBetween r (W e)) :
    IsBlockPositiveBetween r (aggregateLocalWitness weights L R W) := by
  intro X hrank
  rw [aggregateLocalWitness, qform_sum, Complex.re_sum]
  exact Finset.sum_nonneg fun e _ => by
    rw [qform_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    exact mul_nonneg (hweights e)
      (localKrausPullback_isBlockPositiveBetween
        (L e) (R e) (hW e) X hrank)

omit [Fintype A] [Fintype B] in
/-- Nonnegative weighted aggregation of Hermitian witnesses is Hermitian. -/
theorem aggregateLocalWitness_isHermitian
    (weights : E → ℝ)
    (L : E → P → Matrix C A ℂ) (R : E → Q → Matrix D B ℂ)
    {W : E → Matrix (C × D) (C × D) ℂ}
    (hW : ∀ e, (W e).IsHermitian) :
    (aggregateLocalWitness weights L R W).IsHermitian := by
  rw [Matrix.IsHermitian, aggregateLocalWitness, Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl fun e _ => by
    rw [Matrix.conjTranspose_smul]
    rw [(localKrausPullback_isHermitian (L e) (R e) (hW e)).eq]
    rw [RCLike.star_def, Complex.conj_ofReal]

/-- The finite-coordinate local-channel aggregation theorem, stated at the
Kraus level. -/
theorem trace_mul_aggregateLocalWitness_nonneg {r : ℕ}
    {weights : E → ℝ} (hweights : ∀ e, 0 ≤ weights e)
    (L : E → P → Matrix C A ℂ) (R : E → Q → Matrix D B ℂ)
    {W : E → Matrix (C × D) (C × D) ℂ}
    (hWHerm : ∀ e, (W e).IsHermitian)
    (hWBlock : ∀ e, IsBlockPositiveBetween r (W e))
    {ρ : Matrix (A × B) (A × B) ℂ}
    (hρ : SchmidtNumberLEBetween r ρ) :
    0 ≤ ((aggregateLocalWitness weights L R W * ρ).trace).re :=
  trace_mul_nonneg_of_schmidtNumberLEBetween
    (aggregateLocalWitness_isHermitian weights L R hWHerm)
    (aggregateLocalWitness_isBlockPositiveBetween hweights L R hWBlock) hρ

/-- A negative aggregate energy certifies failure of the
Schmidt-number-at-most-`r` promise. -/
theorem not_schmidtNumberLEBetween_of_aggregateLocalWitness_neg {r : ℕ}
    {weights : E → ℝ} (hweights : ∀ e, 0 ≤ weights e)
    (L : E → P → Matrix C A ℂ) (R : E → Q → Matrix D B ℂ)
    {W : E → Matrix (C × D) (C × D) ℂ}
    (hWHerm : ∀ e, (W e).IsHermitian)
    (hWBlock : ∀ e, IsBlockPositiveBetween r (W e))
    {ρ : Matrix (A × B) (A × B) ℂ}
    (hneg : ((aggregateLocalWitness weights L R W * ρ).trace).re < 0) :
    ¬ SchmidtNumberLEBetween r ρ := by
  intro hρ
  exact (not_lt_of_ge
    (trace_mul_aggregateLocalWitness_nonneg
      hweights L R hWHerm hWBlock hρ)) hneg

end Aggregation

section DependentAggregation

variable {A B E : Type*} [Fintype A] [Fintype B] [Fintype E]
  {C D P Q : E → Type*}
  [∀ e, Fintype (C e)] [∀ e, Fintype (D e)]
  [∀ e, Fintype (P e)] [∀ e, Fintype (Q e)]

/-- Local-witness aggregation with output spaces and Kraus index types allowed
to depend on the term `e`. -/
noncomputable def aggregateLocalWitnessDependent
    (weights : E → ℝ)
    (L : (e : E) → P e → Matrix (C e) A ℂ)
    (R : (e : E) → Q e → Matrix (D e) B ℂ)
    (W : (e : E) → Matrix (C e × D e) (C e × D e) ℂ) :
    Matrix (A × B) (A × B) ℂ :=
  ∑ e, (weights e : ℂ) • localKrausPullback (L e) (R e) (W e)

/-- The varying-output aggregation is block positive. -/
theorem aggregateLocalWitnessDependent_isBlockPositiveBetween {r : ℕ}
    {weights : E → ℝ} (hweights : ∀ e, 0 ≤ weights e)
    (L : (e : E) → P e → Matrix (C e) A ℂ)
    (R : (e : E) → Q e → Matrix (D e) B ℂ)
    {W : (e : E) → Matrix (C e × D e) (C e × D e) ℂ}
    (hW : ∀ e, IsBlockPositiveBetween r (W e)) :
    IsBlockPositiveBetween r
      (aggregateLocalWitnessDependent weights L R W) := by
  intro X hrank
  rw [aggregateLocalWitnessDependent, qform_sum, Complex.re_sum]
  exact Finset.sum_nonneg fun e _ => by
    rw [qform_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    exact mul_nonneg (hweights e)
      (localKrausPullback_isBlockPositiveBetween
        (L e) (R e) (hW e) X hrank)

omit [Fintype A] [Fintype B] in
/-- The varying-output aggregation is Hermitian when every output witness is
Hermitian. -/
theorem aggregateLocalWitnessDependent_isHermitian
    (weights : E → ℝ)
    (L : (e : E) → P e → Matrix (C e) A ℂ)
    (R : (e : E) → Q e → Matrix (D e) B ℂ)
    {W : (e : E) → Matrix (C e × D e) (C e × D e) ℂ}
    (hW : ∀ e, (W e).IsHermitian) :
    (aggregateLocalWitnessDependent weights L R W).IsHermitian := by
  rw [Matrix.IsHermitian, aggregateLocalWitnessDependent,
    Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl fun e _ => by
    rw [Matrix.conjTranspose_smul]
    rw [(localKrausPullback_isHermitian (L e) (R e) (hW e)).eq]
    rw [RCLike.star_def, Complex.conj_ofReal]

/-- The local-channel aggregation trace inequality with varying finite output
spaces and varying finite Kraus families. -/
theorem trace_mul_aggregateLocalWitnessDependent_nonneg {r : ℕ}
    {weights : E → ℝ} (hweights : ∀ e, 0 ≤ weights e)
    (L : (e : E) → P e → Matrix (C e) A ℂ)
    (R : (e : E) → Q e → Matrix (D e) B ℂ)
    {W : (e : E) → Matrix (C e × D e) (C e × D e) ℂ}
    (hWHerm : ∀ e, (W e).IsHermitian)
    (hWBlock : ∀ e, IsBlockPositiveBetween r (W e))
    {ρ : Matrix (A × B) (A × B) ℂ}
    (hρ : SchmidtNumberLEBetween r ρ) :
    0 ≤ ((aggregateLocalWitnessDependent weights L R W * ρ).trace).re :=
  trace_mul_nonneg_of_schmidtNumberLEBetween
    (aggregateLocalWitnessDependent_isHermitian weights L R hWHerm)
    (aggregateLocalWitnessDependent_isBlockPositiveBetween
      hweights L R hWBlock) hρ

/-- Negative expectation of the varying-output aggregate certifies failure of
the Schmidt-number-at-most-`r` promise. -/
theorem not_schmidtNumberLEBetween_of_aggregateLocalWitnessDependent_neg
    {r : ℕ}
    {weights : E → ℝ} (hweights : ∀ e, 0 ≤ weights e)
    (L : (e : E) → P e → Matrix (C e) A ℂ)
    (R : (e : E) → Q e → Matrix (D e) B ℂ)
    {W : (e : E) → Matrix (C e × D e) (C e × D e) ℂ}
    (hWHerm : ∀ e, (W e).IsHermitian)
    (hWBlock : ∀ e, IsBlockPositiveBetween r (W e))
    {ρ : Matrix (A × B) (A × B) ℂ}
    (hneg :
      ((aggregateLocalWitnessDependent weights L R W * ρ).trace).re < 0) :
    ¬ SchmidtNumberLEBetween r ρ := by
  intro hρ
  exact (not_lt_of_ge
    (trace_mul_aggregateLocalWitnessDependent_nonneg
      hweights L R hWHerm hWBlock hρ)) hneg

omit [Fintype A] [Fintype B] in
/-- Under trace-preserving local Kraus maps, shifting every output witness by
`μ_e I` shifts the aggregate by exactly `(∑ e, w_e μ_e) I`. -/
theorem aggregateLocalWitnessDependent_shift_eq
    [DecidableEq A] [DecidableEq B]
    [∀ e, DecidableEq (C e)] [∀ e, DecidableEq (D e)]
    (weights mu : E → ℝ)
    (L : (e : E) → P e → Matrix (C e) A ℂ)
    (R : (e : E) → Q e → Matrix (D e) B ℂ)
    (hL : ∀ e, IsTracePreservingKraus (L e))
    (hR : ∀ e, IsTracePreservingKraus (R e))
    (W : (e : E) → Matrix (C e × D e) (C e × D e) ℂ) :
    aggregateLocalWitnessDependent weights L R
        (fun e => W e -
          (mu e : ℂ) •
            (1 : Matrix (C e × D e) (C e × D e) ℂ)) =
      aggregateLocalWitnessDependent weights L R W -
        ((∑ e, weights e * mu e : ℝ) : ℂ) •
          (1 : Matrix (A × B) (A × B) ℂ) := by
  rw [aggregateLocalWitnessDependent, aggregateLocalWitnessDependent]
  calc
    (∑ e, (weights e : ℂ) •
        localKrausPullback (L e) (R e)
          (W e - (mu e : ℂ) •
            (1 : Matrix (C e × D e) (C e × D e) ℂ))) =
      ∑ e, (weights e : ℂ) •
        (localKrausPullback (L e) (R e) (W e) -
          (mu e : ℂ) • (1 : Matrix (A × B) (A × B) ℂ)) := by
            exact Finset.sum_congr rfl fun e _ => by
              rw [localKrausPullback_sub_smul_one
                (L e) (R e) (hL e) (hR e)]
    _ = (∑ e, (weights e : ℂ) •
          localKrausPullback (L e) (R e) (W e)) -
        ((∑ e, weights e * mu e : ℝ) : ℂ) •
          (1 : Matrix (A × B) (A × B) ℂ) := by
            simp_rw [smul_sub, smul_smul]
            rw [Finset.sum_sub_distrib, ← Finset.sum_smul]
            congr 2
            norm_cast

/-- Nonnegative weighted aggregation preserves positivity after each output
witness has been shifted to be positive semidefinite. -/
theorem aggregateLocalWitnessDependent_shift_posSemidef
    [DecidableEq A] [DecidableEq B]
    [∀ e, DecidableEq (C e)] [∀ e, DecidableEq (D e)]
    {weights : E → ℝ} (hweights : ∀ e, 0 ≤ weights e)
    (mu : E → ℝ)
    (L : (e : E) → P e → Matrix (C e) A ℂ)
    (R : (e : E) → Q e → Matrix (D e) B ℂ)
    {W : (e : E) → Matrix (C e × D e) (C e × D e) ℂ}
    (hshift : ∀ e,
      (W e - (mu e : ℂ) •
        (1 : Matrix (C e × D e) (C e × D e) ℂ)).PosSemidef) :
    (aggregateLocalWitnessDependent weights L R
      (fun e => W e - (mu e : ℂ) •
        (1 : Matrix (C e × D e) (C e × D e) ℂ))).PosSemidef := by
  rw [aggregateLocalWitnessDependent]
  exact
    (Finset.sum_nonneg fun e _ =>
      ((localKrausPullback_posSemidef (L e) (R e) (hshift e)).smul
        ((RCLike.ofReal_nonneg (K := ℂ)).mpr (hweights e))).nonneg).posSemidef

/-- For a normalized state of Schmidt number at most `r`, the shifted local
aggregate is bounded below by the explicit scalar baseline
`-∑ e, w_e μ_e`. -/
theorem trace_mul_aggregateLocalWitnessDependent_shift_lower
    [DecidableEq A] [DecidableEq B]
    [∀ e, DecidableEq (C e)] [∀ e, DecidableEq (D e)]
    {r : ℕ} {weights : E → ℝ} (hweights : ∀ e, 0 ≤ weights e)
    (mu : E → ℝ)
    (L : (e : E) → P e → Matrix (C e) A ℂ)
    (R : (e : E) → Q e → Matrix (D e) B ℂ)
    (hL : ∀ e, IsTracePreservingKraus (L e))
    (hR : ∀ e, IsTracePreservingKraus (R e))
    {W : (e : E) → Matrix (C e × D e) (C e × D e) ℂ}
    (hWHerm : ∀ e, (W e).IsHermitian)
    (hWBlock : ∀ e, IsBlockPositiveBetween r (W e))
    {ρ : Matrix (A × B) (A × B) ℂ}
    (hρ : SchmidtNumberLEBetween r ρ) (htrace : ρ.trace = 1) :
    -(∑ e, weights e * mu e) ≤
      ((aggregateLocalWitnessDependent weights L R
        (fun e => W e - (mu e : ℂ) •
          (1 : Matrix (C e × D e) (C e × D e) ℂ)) * ρ).trace).re := by
  have hnonneg :=
    trace_mul_aggregateLocalWitnessDependent_nonneg
      hweights L R hWHerm hWBlock hρ
  rw [aggregateLocalWitnessDependent_shift_eq
    weights mu L R hL hR W]
  simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul,
    Matrix.trace_sub, Matrix.trace_smul, htrace, smul_eq_mul, mul_one]
  change -(∑ e, weights e * mu e) ≤
    (aggregateLocalWitnessDependent weights L R W * ρ).trace.re -
      ∑ e, weights e * mu e
  linarith

end DependentAggregation

section ReductionAggregation

variable {A B E P Q T : Type*}
  [Fintype A] [Fintype B] [Fintype E] [Fintype P] [Fintype Q]
  [Fintype T] [DecidableEq T]

/-- The concrete local witness
`(I - |Ω⟩⟨Ω|/r) ⊗ (I - |Ω⟩⟨Ω|/r)` is `r`-block-positive when
`r ≤ d`. -/
theorem productReductionChoi_inv_isBlockPositiveBetween
    {r : ℕ} (hr : 0 < r) (hrT : r ≤ Fintype.card T)
    (hTtwo : 2 ≤ Fintype.card T) :
    IsBlockPositiveBetween r
      (productReductionChoi (U := T) (V := T)
        (1 / (r : ℝ)) (1 / (r : ℝ))) := by
  change IsBlockPositive r
    (productReductionChoi (U := T) (V := T)
      (1 / (r : ℝ)) (1 / (r : ℝ)))
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  apply (isBlockPositive_productReductionChoi_self_iff_le_inv_min
    hr hTtwo (by positivity)).2
  have hrTR : (r : ℝ) ≤ Fintype.card T := by exact_mod_cast hrT
  rw [min_eq_left hrTR]

/-- The displayed shift by `1 - d/r` makes the concrete local witness positive
semidefinite.  This is the order-theoretic content of the minimum-eigenvalue
claim in the positive-pullback remark. -/
theorem productReductionChoi_inv_shift_posSemidef
    {r : ℕ} (hr : 0 < r) (hrT : r ≤ Fintype.card T) :
    (productReductionChoi (U := T) (V := T)
        (1 / (r : ℝ)) (1 / (r : ℝ))
      - (((1 : ℝ) - Fintype.card T / r : ℝ) : ℂ) • 1).PosSemidef := by
  let γ := traceSeparationGamma (T := T) r
  have hTpos : 0 < Fintype.card T := hr.trans_le hrT
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hγ : 0 ≤ γ := by
    dsimp only [γ, traceSeparationGamma]
    rw [sub_nonneg, le_div_iff₀ hrR]
    have hrTR : (r : ℝ) ≤ Fintype.card T := by exact_mod_cast hrT
    simpa using hrTR
  have heq :
      productReductionChoi (U := T) (V := T)
          (1 / (r : ℝ)) (1 / (r : ℝ))
        - (((1 : ℝ) - Fintype.card T / r : ℝ) : ℂ) • 1 =
      (((1 + γ : ℝ) : ℂ) • twoCopySectorCC (T := T))
        + (((γ + γ ^ 2 : ℝ) : ℂ) • twoCopySectorPP (T := T)) := by
    rw [productReductionChoi_inv_eq_twoCopySectors hr hTpos,
      ← twoCopySectors_sum (T := T)]
    dsimp only [γ, traceSeparationGamma]
    module
  rw [heq]
  exact
    ((twoCopySectorCC_posSemidef hTpos).smul
      ((RCLike.ofReal_nonneg (K := ℂ)).mpr
        (add_nonneg zero_le_one hγ))).add
    ((twoCopySectorPP_posSemidef hTpos).smul
      ((RCLike.ofReal_nonneg (K := ℂ)).mpr
        (add_nonneg hγ (sq_nonneg γ))))

/-- The concrete reduction-product witness is `r`-block-positive throughout
the manuscript range `0 < r ≤ d`, including the degenerate case `d = 1`. -/
theorem productReductionChoi_inv_isBlockPositiveBetween_all
    {r : ℕ} (hr : 0 < r) (hrT : r ≤ Fintype.card T) :
    IsBlockPositiveBetween r
      (productReductionChoi (U := T) (V := T)
        (1 / (r : ℝ)) (1 / (r : ℝ))) := by
  by_cases hTtwo : 2 ≤ Fintype.card T
  · exact productReductionChoi_inv_isBlockPositiveBetween hr hrT hTtwo
  · have hrone : r = 1 := by omega
    have hTone : Fintype.card T = 1 := by omega
    have hpsd :=
      productReductionChoi_inv_shift_posSemidef (T := T) hr hrT
    have hpsd' :
        (productReductionChoi (U := T) (V := T)
          (1 / (r : ℝ)) (1 / (r : ℝ))).PosSemidef := by
      simpa [hrone, hTone] using hpsd
    intro C _
    exact qform_re_nonneg_of_posSemidef hpsd' (vec C)

/-- `μ` is the exact Rayleigh minimum of a finite Hermitian matrix when it is
a lower quadratic-form bound and some nonzero vector attains it.  This
coordinate predicate is the spectral content needed for the manuscript's
`λ_min` notation without choosing an eigenvalue enumeration. -/
def IsExactRayleighMinimum {X : Type*} [Fintype X]
    (μ : ℝ) (W : Matrix X X ℂ) : Prop :=
  (∀ x : EuclideanSpace ℂ X, μ * ‖x‖ ^ 2 ≤ (qform W x).re) ∧
    ∃ x : EuclideanSpace ℂ X, x ≠ 0 ∧
      (qform W x).re = μ * ‖x‖ ^ 2

/-- The reduction-product witness has exact Rayleigh minimum `1 - d/r`
throughout `0 < r ≤ d`.  The proof uses the shifted positive decomposition
for the lower bound and the manuscript's explicit score extremizers for
attainment. -/
theorem productReductionChoi_inv_exactRayleighMinimum
    {r : ℕ} (hr : 0 < r) (hrT : r ≤ Fintype.card T) :
    IsExactRayleighMinimum
      ((1 : ℝ) - Fintype.card T / r)
      (productReductionChoi (U := T) (V := T)
        (1 / (r : ℝ)) (1 / (r : ℝ))) := by
  have hTpos : 0 < Fintype.card T := hr.trans_le hrT
  constructor
  · intro x
    have hq := qform_re_nonneg_of_posSemidef
      (productReductionChoi_inv_shift_posSemidef
        (T := T) hr hrT) x
    rw [qform_sub, qform_smul, qform_one, Complex.sub_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] at hq
    exact sub_nonneg.mp hq
  · let S : Finset T := Finset.univ
    by_cases hTtwo : 2 ≤ Fintype.card T
    · obtain ⟨x₀, x₁, hx⟩ :=
        Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card T)
      let C : Matrix (T × T) (T × T) ℂ := projWit S x₀ x₁
      have hC : C ≠ 0 := by
        intro hzero
        have hnorm := hsNormSq_projWit (S := S) x₀ x₁
        change projWit S x₀ x₁ = 0 at hzero
        rw [hzero] at hnorm
        have hcardzero : (0 : ℝ) = Fintype.card T := by
          simpa [S, hsNormSq] using hnorm
        have hcardpos : (0 : ℝ) < Fintype.card T := by
          exact_mod_cast hTpos
        linarith
      have hvec : vec C ≠ 0 := fun h => hC (by
        ext i j
        have happ := congrFun (congrArg WithLp.ofLp h) (i, j)
        simpa using happ)
      refine ⟨vec C, hvec, ?_⟩
      rw [productReductionChoi_self_eq_twoCopyScoreOperator,
        re_qform_twoCopyScoreOperator,
        twoCopyScore_projWit_orthogonal
          (S := S) (r := Fintype.card T) hx (by simp [S]),
        hsNormSq_eq_norm_sq]
      simp only [C]
      ring
    · have hrone : r = 1 := by omega
      have hTone : Fintype.card T = 1 := by omega
      let x : T := Classical.choice (Fintype.card_pos_iff.mp hTpos)
      let C : Matrix (T × T) (T × T) ℂ := projWit S x x
      have hC : C ≠ 0 := by
        intro hzero
        have hnorm := hsNormSq_projWit (S := S) x x
        change projWit S x x = 0 at hzero
        rw [hzero] at hnorm
        simp [S, hTone, hsNormSq] at hnorm
      have hvec : vec C ≠ 0 := fun h => hC (by
        ext i j
        have happ := congrFun (congrArg WithLp.ofLp h) (i, j)
        simpa using happ)
      refine ⟨vec C, hvec, ?_⟩
      rw [productReductionChoi_self_eq_twoCopyScoreOperator,
        re_qform_twoCopyScoreOperator,
        twoCopyScore_projWit_same (S := S) (r := Fintype.card T)
          (by simp [S]) (1 / (r : ℝ)),
        hsNormSq_eq_norm_sq]
      simp [hrone, hTone]

/-- The local-Hamiltonian Schmidt-number certificate for a common local
coordinate dimension.  Arbitrary local Kraus families are allowed; channel
normalization is not required for the implication. -/
theorem not_schmidtNumberLEBetween_of_reductionAggregate_neg
    {r : ℕ} (hr : 0 < r) (hrT : r ≤ Fintype.card T)
    {weights : E → ℝ} (hweights : ∀ e, 0 ≤ weights e)
    (L : E → P → Matrix (T × T) A ℂ)
    (R : E → Q → Matrix (T × T) B ℂ)
    {ρ : Matrix (A × B) (A × B) ℂ}
    (hneg :
      ((aggregateLocalWitness weights L R
        (fun _ => productReductionChoi (U := T) (V := T)
          (1 / (r : ℝ)) (1 / (r : ℝ))) * ρ).trace).re < 0) :
    ¬ SchmidtNumberLEBetween r ρ := by
  apply not_schmidtNumberLEBetween_of_aggregateLocalWitness_neg
    (W := fun _ => productReductionChoi (U := T) (V := T)
      (1 / (r : ℝ)) (1 / (r : ℝ)))
    hweights L R
  · intro e
    exact productReductionChoi_isHermitian (U := T) (V := T) _ _
  · intro e
    exact productReductionChoi_inv_isBlockPositiveBetween_all hr hrT
  · exact hneg

end ReductionAggregation

section DependentReductionAggregation

variable {A B E : Type*} [Fintype A] [Fintype B] [Fintype E]
  {T P Q : E → Type*}
  [∀ e, Fintype (T e)] [∀ e, DecidableEq (T e)]
  [∀ e, Fintype (P e)] [∀ e, Fintype (Q e)]

/-- The local-Hamiltonian certificate with the local matched dimension and
both Kraus index types allowed to vary with the term. -/
theorem not_schmidtNumberLEBetween_of_dependentReductionAggregate_neg
    {r : ℕ} (hr : 0 < r)
    (hrT : ∀ e, r ≤ Fintype.card (T e))
    {weights : E → ℝ} (hweights : ∀ e, 0 ≤ weights e)
    (L : (e : E) → P e → Matrix (T e × T e) A ℂ)
    (R : (e : E) → Q e → Matrix (T e × T e) B ℂ)
    {ρ : Matrix (A × B) (A × B) ℂ}
    (hneg :
      ((aggregateLocalWitnessDependent weights L R
        (fun e => productReductionChoi (U := T e) (V := T e)
          (1 / (r : ℝ)) (1 / (r : ℝ))) * ρ).trace).re < 0) :
    ¬ SchmidtNumberLEBetween r ρ := by
  apply not_schmidtNumberLEBetween_of_aggregateLocalWitnessDependent_neg
    (W := fun e => productReductionChoi (U := T e) (V := T e)
      (1 / (r : ℝ)) (1 / (r : ℝ)))
    hweights L R
  · intro e
    exact productReductionChoi_isHermitian (U := T e) (V := T e) _ _
  · intro e
    exact productReductionChoi_inv_isBlockPositiveBetween_all hr (hrT e)
  · exact hneg

/-- The weighted aggregate of the concretely shifted reduction-product
witnesses is positive semidefinite. -/
theorem dependentReductionAggregate_shift_posSemidef
    [DecidableEq A] [DecidableEq B]
    {r : ℕ} (hr : 0 < r)
    (hrT : ∀ e, r ≤ Fintype.card (T e))
    {weights : E → ℝ} (hweights : ∀ e, 0 ≤ weights e)
    (L : (e : E) → P e → Matrix (T e × T e) A ℂ)
    (R : (e : E) → Q e → Matrix (T e × T e) B ℂ) :
    (aggregateLocalWitnessDependent weights L R
      (fun e =>
        productReductionChoi (U := T e) (V := T e)
            (1 / (r : ℝ)) (1 / (r : ℝ)) -
          (((1 : ℝ) - Fintype.card (T e) / r : ℝ) : ℂ) •
            (1 : Matrix
              ((T e × T e) × (T e × T e))
              ((T e × T e) × (T e × T e)) ℂ))).PosSemidef := by
  apply aggregateLocalWitnessDependent_shift_posSemidef
    hweights
    (mu := fun e => (1 : ℝ) - Fintype.card (T e) / r)
    L R
  intro e
  exact productReductionChoi_inv_shift_posSemidef hr (hrT e)

/-- The concrete reduction-product construction has the explicit normalized
energy baseline `∑ e, w_e (d_e / r - 1)`. -/
theorem trace_mul_dependentReductionAggregate_shift_lower
    [DecidableEq A] [DecidableEq B]
    {r : ℕ} (hr : 0 < r)
    (hrT : ∀ e, r ≤ Fintype.card (T e))
    {weights : E → ℝ} (hweights : ∀ e, 0 ≤ weights e)
    (L : (e : E) → P e → Matrix (T e × T e) A ℂ)
    (R : (e : E) → Q e → Matrix (T e × T e) B ℂ)
    (hL : ∀ e, IsTracePreservingKraus (L e))
    (hR : ∀ e, IsTracePreservingKraus (R e))
    {ρ : Matrix (A × B) (A × B) ℂ}
    (hρ : SchmidtNumberLEBetween r ρ) (htrace : ρ.trace = 1) :
    (∑ e, weights e *
      (Fintype.card (T e) / r - 1 : ℝ)) ≤
      ((aggregateLocalWitnessDependent weights L R
        (fun e =>
          productReductionChoi (U := T e) (V := T e)
              (1 / (r : ℝ)) (1 / (r : ℝ)) -
            (((1 : ℝ) - Fintype.card (T e) / r : ℝ) : ℂ) •
              (1 : Matrix
                ((T e × T e) × (T e × T e))
                ((T e × T e) × (T e × T e)) ℂ)) * ρ).trace).re := by
  have hbase :=
    trace_mul_aggregateLocalWitnessDependent_shift_lower
      hweights
      (mu := fun e => (1 : ℝ) - Fintype.card (T e) / r)
      L R hL hR
      (W := fun e =>
        productReductionChoi (U := T e) (V := T e)
          (1 / (r : ℝ)) (1 / (r : ℝ)))
      (fun e => productReductionChoi_isHermitian
        (U := T e) (V := T e) _ _)
      (fun e => productReductionChoi_inv_isBlockPositiveBetween_all
        hr (hrT e))
      hρ htrace
  convert hbase using 1
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun e _ => by ring

end DependentReductionAggregation

end RankR
