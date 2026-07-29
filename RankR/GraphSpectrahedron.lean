/-
The finite-coordinate free-spectrahedral dictionary for the two-layer graph
operator system.

The paper presents the dictionary through a real basis of the traceless
self-adjoint part of an operator system and the associated monic pencils.  The
mathematical content is basis-free: at level `L`, take the positive cone in
`M_L(S)`, and compare it with the inverse image of the positive cone under the
ampliated map.  This file formalizes that basis-free statement, connects the
Choi and actual-map renderings of the corrected graph map, and proves the exact
clique threshold and adjacent-level separation.
-/
import RankR.GraphLayers

namespace RankR

open Matrix Finset ComplexConjugate
open scoped ComplexOrder MatrixOrder

section ChoiInverse

variable {I O : Type*} [Fintype I] [Fintype O]
  [DecidableEq I] [DecidableEq O]

omit [Fintype O] [DecidableEq O] in
/-- Reconstructing a complex-linear coordinate map from its Choi matrix
recovers the map. -/
theorem mapOfChoi_mapChoi
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (X : Matrix I I ℂ) :
    mapOfChoi (mapChoi Φ) X = Φ X := by
  have hX :
      (∑ i : I, ∑ j : I,
        X i j • Matrix.single i j (1 : ℂ)) = X := by
    simp_rw [Matrix.smul_single]
    simpa using (matrix_eq_sum_single X).symm
  conv_rhs => rw [← hX]
  rw [map_sum]
  simp_rw [map_sum, map_smul]
  ext o p
  simp [mapOfChoi, mapChoi, Matrix.sum_apply, Matrix.smul_apply]

omit [Fintype O] [DecidableEq O] in
/-- The bundled version of `mapOfChoi_mapChoi`. -/
theorem mapOfChoiLinear_mapChoi
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) :
    mapOfChoiLinear (mapChoi Φ) = Φ := by
  ext X o p
  exact congrArg (fun M => M o p) (mapOfChoi_mapChoi Φ X)

end ChoiInverse

section TransposedKrausChoi

variable {W ι : Type*} [Fintype W] [Fintype ι] [DecidableEq W]

private theorem sum5_perm
    {A B C D E M : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E]
    [AddCommMonoid M] (F : A → B → C → D → E → M) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, F a b c d e)
      = ∑ e, ∑ c, ∑ a, ∑ b, ∑ d, F a b c d e := by
  calc
    _ = ∑ a, ∑ b, ∑ c, ∑ e, ∑ d, F a b c d e := by
      exact Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ =>
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ e, ∑ c, ∑ d, F a b c d e := by
      exact Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a, ∑ e, ∑ b, ∑ c, ∑ d, F a b c d e := by
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ e, ∑ a, ∑ b, ∑ c, ∑ d, F a b c d e :=
      Finset.sum_comm
    _ = ∑ e, ∑ a, ∑ c, ∑ b, ∑ d, F a b c d e := by
      exact Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ e, ∑ c, ∑ a, ∑ b, ∑ d, F a b c d e := by
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- A matrix unit passed through a transposed Kraus sum, entrywise. -/
theorem krausSum_transpose_single_apply
    (A : ι → Matrix W W ℂ) (i j o p : W) :
    krausSum A (Matrix.single i j (1 : ℂ))ᵀ o p
      = ∑ a, A a o j * conj (A a p i) := by
  simp [krausSum, Matrix.sum_apply, Matrix.transpose_single,
    mul_single_one_mul_apply, Matrix.conjTranspose_apply,
    RCLike.star_def]

/-- The Choi quadratic form of a transposed Kraus sum is `thetaPair`, with a
transpose caused by the output-first Choi convention. -/
theorem qform_mapChoi_krausSum_transpose
    (A : ι → Matrix W W ℂ) (C : Matrix W W ℂ) :
    qform (mapChoi (fun X => krausSum A Xᵀ)) (vec C)
      = thetaPair A Cᵀ := by
  calc
    qform (mapChoi (fun X => krausSum A Xᵀ)) (vec C)
        =
      ∑ o, ∑ i, ∑ p, ∑ j, ∑ a,
        conj (C o i) * A a o j * conj (A a p i) * C p j := by
          simp only [qform, mapChoi, Matrix.of_apply, vec_apply,
            krausSum_transpose_single_apply, Finset.mul_sum,
            Finset.sum_mul,
            Fintype.sum_prod_type]
          ring_nf
    _ =
      ∑ a, ∑ p, ∑ o, ∑ i, ∑ j,
        conj (C o i) * A a o j * conj (A a p i) * C p j :=
      sum5_perm fun o i p j a =>
        conj (C o i) * A a o j * conj (A a p i) * C p j
    _ = thetaPair A Cᵀ := by
      rw [thetaPair]
      simp only [hsInner_eq_sum_vec, Fintype.sum_prod_type, vec_apply,
        Matrix.mul_apply, Matrix.transpose_apply, map_sum, map_mul]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro o _
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- The Choi matrix of a transposed Kraus sum is Hermitian. -/
theorem mapChoi_krausSum_transpose_isHermitian
    (A : ι → Matrix W W ℂ) :
    (mapChoi (fun X => krausSum A Xᵀ)).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext ⟨o, i⟩ ⟨p, j⟩
  simp only [Matrix.conjTranspose_apply, mapChoi, Matrix.of_apply,
    krausSum_transpose_single_apply]
  change
    conj (∑ a, A a p i * conj (A a o j))
      = ∑ a, A a o j * conj (A a p i)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [map_mul, Complex.conj_conj]
  ring

end TransposedKrausChoi

section GraphThetaLinear

variable {U : Type*} [Fintype U] [DecidableEq U] [LinearOrder U]

/-- The corrected graph map as a complex-linear coordinate map. -/
noncomputable def graphThetaLinear
    (E : Finset (U × U)) (R : ℕ) (lam : ℂ) :
    Matrix (U × Fin 2) (U × Fin 2) ℂ →ₗ[ℂ]
      Matrix (U × Fin 2) (U × Fin 2) ℂ where
  toFun := graphTheta E R lam
  map_add' := by
    intro X Y
    ext i j
    simp [graphTheta, graphPhiTranspose, krausSum, Matrix.add_apply,
      Matrix.transpose_add, Matrix.trace_add, Matrix.sum_apply,
      Finset.sum_add_distrib, add_mul, mul_add]
    ring
  map_smul' := by
    intro c X
    ext i j
    simp [graphTheta, graphPhiTranspose, krausSum, Matrix.smul_apply,
      Matrix.transpose_smul, Matrix.trace_smul, Matrix.sum_apply,
      mul_assoc]
    rw [mul_add, Finset.mul_sum]
    ring

omit [LinearOrder U] in
@[simp] theorem graphThetaLinear_apply
    (E : Finset (U × U)) (R : ℕ) (lam : ℂ)
    (X : Matrix (U × Fin 2) (U × Fin 2) ℂ) :
    graphThetaLinear E R lam X = graphTheta E R lam X :=
  rfl

omit [LinearOrder U] in
/-- The Choi matrix unit of the transposed graph Kraus map, entrywise. -/
theorem graphPhiTranspose_single_apply
    (E : Finset (U × U)) (i j o p : U × Fin 2) :
    graphPhiTranspose E (Matrix.single i j (1 : ℂ)) o p
      =
    ∑ a : {e : U × U // e ∈ E},
      graphKraus E a o j * conj (graphKraus E a p i) := by
  simp [graphPhiTranspose, krausSum, Matrix.sum_apply,
    Matrix.transpose_single, mul_single_one_mul_apply,
    Matrix.conjTranspose_apply, RCLike.star_def]

omit [LinearOrder U] in
/-- The Choi quadratic form of `Φ_G ∘ τ` is `thetaPair`, with a transpose
caused by the output-first Choi convention. -/
theorem qform_mapChoi_graphPhiTranspose
    (E : Finset (U × U))
    (C : Matrix (U × Fin 2) (U × Fin 2) ℂ) :
    qform (mapChoi (graphPhiTranspose E)) (vec C)
      = thetaPair (graphKraus E) Cᵀ := by
  exact qform_mapChoi_krausSum_transpose (graphKraus E) C

omit [LinearOrder U] in
/-- Choi matrix of the actual corrected graph map. -/
theorem mapChoi_graphThetaLinear
    (E : Finset (U × U)) (R : ℕ) (lam : ℂ) :
    mapChoi (graphThetaLinear E R lam)
      =
    mapChoi (graphPhiTranspose E)
      + lam • ((1 : Matrix
          ((U × Fin 2) × (U × Fin 2))
          ((U × Fin 2) × (U × Fin 2)) ℂ)
        - (R : ℂ)⁻¹ • singleOmegaChoi) := by
  ext ⟨o, i⟩ ⟨p, j⟩
  simp only [mapChoi, Matrix.of_apply, graphThetaLinear_apply, graphTheta,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply]
  by_cases hij : i = j
  · subst j
    rw [Matrix.trace_single_eq_same]
    simp only [Matrix.one_apply, singleOmegaChoi, rankOne,
      singleOmegaVec_apply, Matrix.single_apply, Matrix.of_apply]
    by_cases hoi : o = i <;> by_cases hip : i = p <;>
      simp [hoi, hip, eq_comm]
  · rw [Matrix.trace_single_eq_of_ne i j (1 : ℂ) hij]
    simp [Matrix.one_apply, singleOmegaChoi, rankOne,
      singleOmegaVec_apply, Matrix.single_apply, hij, eq_comm]
    split_ifs <;> simp_all

omit [LinearOrder U] in
/-- The Choi quadratic form of the corrected graph map is exactly the
unrolled expression used by `ThetaPositive`. -/
theorem re_qform_mapChoi_graphThetaLinear
    (E : Finset (U × U)) (R : ℕ) (lam : ℝ)
    (C : Matrix (U × Fin 2) (U × Fin 2) ℂ) :
    (qform (mapChoi (graphThetaLinear E R (lam : ℂ))) (vec C)).re
      =
    (thetaPair (graphKraus E) Cᵀ).re
      + lam * (hsNormSq C - Complex.normSq C.trace / R) := by
  rw [mapChoi_graphThetaLinear, qform_add, qform_smul,
    qform_sub, qform_smul, qform_one, singleOmegaChoi,
    qform_rankOne, inner_singleOmegaVec,
    qform_mapChoi_graphPhiTranspose, hsNormSq_eq_norm_sq]
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [show ((R : ℂ)⁻¹).re = (R : ℝ)⁻¹ by
    change (((R : ℝ) : ℂ)⁻¹).re = (R : ℝ)⁻¹
    rw [← Complex.ofReal_inv]
    rfl]
  ring

omit [LinearOrder U] in
theorem mapChoi_graphThetaLinear_isHermitian
    (E : Finset (U × U)) (R : ℕ) (lam : ℝ) :
    (mapChoi (graphThetaLinear E R (lam : ℂ))).IsHermitian := by
  have hPhi :=
    mapChoi_krausSum_transpose_isHermitian (graphKraus E)
  rw [Matrix.IsHermitian] at hPhi
  have hPhi' :
      (mapChoi (graphPhiTranspose E))ᴴ
        = mapChoi (graphPhiTranspose E) := by
    change
      (mapChoi (fun X => krausSum (graphKraus E) Xᵀ))ᴴ
        = mapChoi (fun X => krausSum (graphKraus E) Xᵀ)
    exact hPhi
  rw [Matrix.IsHermitian]
  rw [mapChoi_graphThetaLinear, Matrix.conjTranspose_add,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hPhi']
  simp [singleOmegaChoi, rankOne_conjTranspose]

omit [LinearOrder U] in
/-- The unrolled `ThetaPositive` predicate is exactly block positivity of the
actual corrected graph map's Choi matrix. -/
theorem isBlockPositive_mapChoi_graphThetaLinear_iff
    (E : Finset (U × U)) (R : ℕ) (lam : ℝ) :
    IsBlockPositive R
        (mapChoi (graphThetaLinear E R (lam : ℂ)))
      ↔ ThetaPositive (graphKraus E) R lam := by
  constructor
  · intro h C hC
    have hCT := h Cᵀ (by simpa only [Matrix.rank_transpose] using hC)
    rw [re_qform_mapChoi_graphThetaLinear] at hCT
    simpa only [Matrix.transpose_transpose, hsNormSq_transpose,
      Matrix.trace_transpose] using hCT
  · intro h C hC
    rw [re_qform_mapChoi_graphThetaLinear]
    have hCT := h Cᵀ (by simpa only [Matrix.rank_transpose] using hC)
    simpa only [hsNormSq_transpose, Matrix.trace_transpose] using hCT

end GraphThetaLinear

/-! ## Positivity of arbitrary finite ampliations -/

section ArbitraryLevelPositivity

variable {A W : Type*} [Fintype A] [Fintype W]
  [DecidableEq A] [DecidableEq W]

/-- Positivity of an actual coordinate ampliation at an arbitrary finite
ancilla type. -/
def IsMapPositiveAt
    (A : Type*) [Fintype A]
    (Φ : Matrix W W ℂ →ₗ[ℂ] Matrix W W ℂ) : Prop :=
  ∀ X : Matrix (A × W) (A × W) ℂ, X.PosSemidef →
    (mapAmplification (A := A) Φ X).PosSemidef

omit [DecidableEq W] in
/-- Block positivity is monotone in its allowed matrix rank. -/
theorem isBlockPositive_mono
    {r s : ℕ} {M : Matrix (W × W) (W × W) ℂ}
    (h : IsBlockPositive r M) (hsr : s ≤ r) :
    IsBlockPositive s M := by
  intro C hC
  exact h C (hC.trans hsr)

/-- Choi block positivity through the cardinality of an arbitrary finite
ancilla implies positivity of that ampliation. -/
theorem isMapPositiveAt_mapOfChoi_of_isBlockPositive
    {M : Matrix (W × W) (W × W) ℂ} (hM : M.IsHermitian)
    (hblock : IsBlockPositive (Fintype.card A) M) :
    IsMapPositiveAt A (mapOfChoiLinear M) := by
  intro X hX
  obtain ⟨B, hB⟩ :=
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hX.nonneg
  have hB' : X = Bᴴ * B := by
    simpa [star_eq_conjTranspose] using hB
  rw [hB', ← sum_rankOne_conjRow_eq_conjTranspose_mul]
  change
    (mapAmplificationLinear (A := A) (mapOfChoiLinear M)
      (∑ k : A × W,
        rankOne
          (WithLp.toLp 2 fun p => conj (B k p))
          (WithLp.toLp 2 fun p => conj (B k p)))).PosSemidef
  rw [map_sum]
  exact (Finset.sum_nonneg fun k _ =>
    (mapAmplification_mapOfChoi_rankOne_posSemidef
      hM hblock
      (WithLp.toLp 2 fun p => conj (B k p))).nonneg).posSemidef

/-- The same implication for an arbitrary linear map, obtained by the
coordinate Choi inverse. -/
theorem isMapPositiveAt_of_isBlockPositive_mapChoi
    (Φ : Matrix W W ℂ →ₗ[ℂ] Matrix W W ℂ)
    (hM : (mapChoi Φ).IsHermitian)
    (hblock : IsBlockPositive (Fintype.card A) (mapChoi Φ)) :
    IsMapPositiveAt A Φ := by
  rw [← mapOfChoiLinear_mapChoi Φ]
  exact isMapPositiveAt_mapOfChoi_of_isBlockPositive hM hblock

end ArbitraryLevelPositivity

section GraphMapPositivity

variable {U A : Type*} [Fintype U] [Fintype A]
  [DecidableEq U] [DecidableEq A] [LinearOrder U]

omit [LinearOrder U] in
/-- Choi-form positivity of the corrected graph map implies positivity of its
actual ampliation at every ancilla whose cardinality fits under the protected
rank. -/
theorem isMapPositiveAt_graphThetaLinear_of_thetaPositive
    (E : Finset (U × U)) {R : ℕ} (lam : ℝ)
    (hTheta : ThetaPositive (graphKraus E) R lam)
    (hcard : Fintype.card A ≤ R) :
    IsMapPositiveAt A (graphThetaLinear E R (lam : ℂ)) := by
  exact isMapPositiveAt_of_isBlockPositive_mapChoi
    (graphThetaLinear E R (lam : ℂ))
    (mapChoi_graphThetaLinear_isHermitian E R lam)
    (isBlockPositive_mono
      ((isBlockPositive_mapChoi_graphThetaLinear_iff E R lam).2 hTheta)
      hcard)

end GraphMapPositivity

/-! ## The basis-free inclusion dictionary -/

section PositiveConeDictionary

variable {L W : Type*} [Fintype L] [Fintype W]

/-- The positive cone at matrix level `L` of a matrix subspace `S`. -/
def matrixLevelPositiveCone
    (S : Submodule ℂ (Matrix W W ℂ))
    (Z : Matrix (L × W) (L × W) ℂ) : Prop :=
  Z ∈ matrixLevelSpace S ∧ Z.PosSemidef

/-- The positivity locus obtained by applying a coefficient map at level `L`.

The domain condition is the basis-free version of the monic pencil locus; the
second condition is positivity of the image pencil. -/
def mappedMatrixLevelPositiveCone
    (S : Submodule ℂ (Matrix W W ℂ))
    (Φ : Matrix W W ℂ → Matrix W W ℂ)
    (Z : Matrix (L × W) (L × W) ℂ) : Prop :=
  matrixLevelPositiveCone S Z ∧
    (mapAmplification (A := L) Φ Z).PosSemidef

omit [Fintype L] [Fintype W] in
/-- Inclusion of the positive matrix-level cone in its mapped positivity locus
is exactly positivity of the restricted ampliation. -/
theorem matrixLevelPositiveCone_subset_mapped_iff
    (S : Submodule ℂ (Matrix W W ℂ))
    (Φ : Matrix W W ℂ → Matrix W W ℂ) :
    (∀ Z : Matrix (L × W) (L × W) ℂ,
      matrixLevelPositiveCone S Z →
        mappedMatrixLevelPositiveCone S Φ Z)
      ↔
    ∀ Z : Matrix (L × W) (L × W) ℂ,
      Z ∈ matrixLevelSpace S → Z.PosSemidef →
        (mapAmplification (A := L) Φ Z).PosSemidef := by
  constructor
  · intro h Z hZS hZ
    exact (h Z ⟨hZS, hZ⟩).2
  · intro h Z hZ
    exact ⟨hZ, h Z hZ.1 hZ.2⟩

end PositiveConeDictionary

/-! ## Padding and compression between matrix levels -/

section LevelPadding

variable {K L W : Type*} [Fintype K] [Fintype L] [Fintype W]
  [DecidableEq K] [DecidableEq L] [DecidableEq W]

private theorem sum_pair_indicator
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {M : Type*} [AddCommMonoid M]
    (a : A) (b : B) (f : A → B → M) :
    (∑ x, ∑ y, if a = x ∧ b = y then f x y else 0) = f a b := by
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro y _ hy
      simp [Ne.symm hy]
    · simp
  · intro x _ hx
    simp [Ne.symm hx]
  · simp

/-- The coordinate isometry induced by an embedding of matrix-level indices. -/
def levelEmbedding (e : K ↪ L) :
    Matrix (L × W) (K × W) ℂ :=
  Matrix.of fun p q =>
    if p.1 = e q.1 ∧ p.2 = q.2 then 1 else 0

/-- Pad a matrix at level `K` by zeros into a larger level `L`. -/
noncomputable def padMatrixLevel
    (e : K ↪ L) (Z : Matrix (K × W) (K × W) ℂ) :
    Matrix (L × W) (L × W) ℂ :=
  levelEmbedding e * Z * (levelEmbedding e)ᴴ

omit [Fintype L] in
/-- A padded matrix recovers its original coefficient blocks on the embedded
level indices. -/
theorem matrixLevelBlock_padMatrixLevel_at
    (e : K ↪ L) (Z : Matrix (K × W) (K × W) ℂ)
    (a b : K) :
    matrixLevelBlock (padMatrixLevel e Z) (e a) (e b)
      = matrixLevelBlock Z a b := by
  ext x y
  simp [matrixLevelBlock, padMatrixLevel, levelEmbedding,
    Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, e.injective.eq_iff,
    RCLike.star_def]
  rw [sum_pair_indicator b y, sum_pair_indicator a x]

omit [Fintype L] in
/-- Every coefficient block of a padded matrix is a finite linear combination
of the original coefficient blocks. -/
theorem matrixLevelBlock_padMatrixLevel
    (e : K ↪ L) (Z : Matrix (K × W) (K × W) ℂ)
    (a b : L) :
    matrixLevelBlock (padMatrixLevel e Z) a b
      =
    ∑ k : K, ∑ l : K,
      (if a = e k ∧ b = e l then (1 : ℂ) else 0)
        • matrixLevelBlock Z k l := by
  by_cases ha : ∃ k, a = e k
  · rcases ha with ⟨k, rfl⟩
    by_cases hb : ∃ l, b = e l
    · rcases hb with ⟨l, rfl⟩
      rw [matrixLevelBlock_padMatrixLevel_at]
      simp only [e.injective.eq_iff, ite_smul, one_smul, zero_smul]
      symm
      exact sum_pair_indicator k l fun x y =>
        matrixLevelBlock Z x y
    · push Not at hb
      ext x y
      simp [matrixLevelBlock, padMatrixLevel, levelEmbedding,
        Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.sum_apply, Fintype.sum_prod_type,
        e.injective.eq_iff, hb]
  · push Not at ha
    ext x y
    simp [matrixLevelBlock, padMatrixLevel, levelEmbedding,
      Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.sum_apply,
      ha, RCLike.star_def]

omit [Fintype L] in
/-- Padding preserves membership in a matrix-level subspace. -/
theorem padMatrixLevel_mem
    (e : K ↪ L) {S : Submodule ℂ (Matrix W W ℂ)}
    {Z : Matrix (K × W) (K × W) ℂ}
    (hZ : Z ∈ matrixLevelSpace S) :
    padMatrixLevel e Z ∈ matrixLevelSpace S := by
  intro a b
  rw [matrixLevelBlock_padMatrixLevel]
  exact Submodule.sum_mem _ fun k _ =>
    Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hZ k l)

omit [DecidableEq K] in
/-- Padding preserves positive semidefiniteness. -/
theorem padMatrixLevel_posSemidef
    (e : K ↪ L) {Z : Matrix (K × W) (K × W) ℂ}
    (hZ : Z.PosSemidef) :
    (padMatrixLevel e Z).PosSemidef :=
  hZ.mul_mul_conjTranspose_same (levelEmbedding e)

end LevelPadding

section GraphInclusion

variable {U L : Type*} [Fintype U] [Fintype L]
  [DecidableEq U] [DecidableEq L] [LinearOrder U]

/-- Basis-free form of the graph note's free-spectrahedral inclusion at the
finite level `L`. -/
def GraphLevelInclusion
    (E : Finset (U × U)) (R : ℕ) (lam : ℝ) : Prop :=
  ∀ Z : Matrix (L × (U × Fin 2)) (L × (U × Fin 2)) ℂ,
    matrixLevelPositiveCone (graphTwoLayerSpace E) Z →
      mappedMatrixLevelPositiveCone
        (graphTwoLayerSpace E)
        (graphThetaLinear E R (lam : ℂ)) Z

omit [LinearOrder U] in
/-- Matrix-level inclusion is downward closed under embeddings of the level
index type. -/
theorem graphLevelInclusion_of_embedding
    {K : Type*} [Fintype K] [DecidableEq K]
    (e : K ↪ L) {E : Finset (U × U)} {R : ℕ} {lam : ℝ}
    (hinc : GraphLevelInclusion (U := U) (L := L) E R lam) :
    GraphLevelInclusion (U := U) (L := K) E R lam := by
  intro Z hZ
  let Zpad := padMatrixLevel (W := U × Fin 2) e Z
  have hZpadSpace :
      Zpad ∈ matrixLevelSpace (graphTwoLayerSpace E) :=
    padMatrixLevel_mem e hZ.1
  have hZpadPos : Zpad.PosSemidef :=
    padMatrixLevel_posSemidef e hZ.2
  have hout :=
    (hinc Zpad ⟨hZpadSpace, hZpadPos⟩).2
  have hsub :
      (mapAmplification (A := L)
          (graphThetaLinear E R (lam : ℂ)) Zpad).submatrix
        (fun p : K × (U × Fin 2) => (e p.1, p.2))
        (fun p : K × (U × Fin 2) => (e p.1, p.2))
        =
      mapAmplification (A := K)
        (graphThetaLinear E R (lam : ℂ)) Z := by
    ext ⟨a, x⟩ ⟨b, y⟩
    change
      graphThetaLinear E R (lam : ℂ)
          (matrixLevelBlock Zpad (e a) (e b)) x y
        =
      graphThetaLinear E R (lam : ℂ)
          (matrixLevelBlock Z a b) x y
    rw [matrixLevelBlock_padMatrixLevel_at]
  refine ⟨hZ, ?_⟩
  rw [← hsub]
  exact hout.submatrix _

omit [DecidableEq L] [LinearOrder U] in
/-- Global positivity of an ampliation implies the restricted
free-spectrahedral inclusion. -/
theorem graphLevelInclusion_of_isMapPositiveAt
    (E : Finset (U × U)) (R : ℕ) (lam : ℝ)
    (h : IsMapPositiveAt L (graphThetaLinear E R (lam : ℂ))) :
    GraphLevelInclusion (L := L) E R lam := by
  intro Z hZ
  exact ⟨hZ, h Z hZ.2⟩

/-- At the protected threshold `λ=R-1`, inclusion holds at every finite level
whose cardinality is at most `R`. -/
theorem graphLevelInclusion_at_threshold_of_card_le
    {E : Finset (U × U)} (hE : ∀ p ∈ E, p.1 < p.2)
    {R : ℕ} (_hR : 0 < R) (hcard : Fintype.card L ≤ R) :
    GraphLevelInclusion (U := U) (L := L) E R ((R : ℝ) - 1) := by
  have hTheta :
      ThetaPositive (graphKraus E) R ((R : ℝ) - 1) := by
    have h :=
      thetaPositive_of_choiTwoBound
        (A := graphKraus E) (β := 1) zero_le_one
        (choiTwoBound_graphKraus hE)
        (graphKraus_transpose E) R
    simpa using h
  exact graphLevelInclusion_of_isMapPositiveAt E R ((R : ℝ) - 1)
    (isMapPositiveAt_graphThetaLinear_of_thetaPositive
      E ((R : ℝ) - 1) hTheta hcard)

omit [DecidableEq U] [LinearOrder U] in
/-- Positive semidefiniteness makes every quadratic form nonnegative. -/
theorem re_qform_nonneg_of_posSemidef
    {W : Type*} [Fintype W]
    {M : Matrix W W ℂ} (hM : M.PosSemidef)
    (x : EuclideanSpace ℂ W) :
    0 ≤ (qform M x).re := by
  have hdot :=
    hM.dotProduct_mulVec_nonneg (x : W → ℂ)
  have heq :
      star (x : W → ℂ) ⬝ᵥ (M *ᵥ (x : W → ℂ))
        = qform M x := by
    simp [qform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [heq] at hdot
  exact (Complex.nonneg_iff.mp hdot).1

/-- A nonempty clique of size `s` obstructs inclusion whenever
`λ < s-1`, independently of the protected rank parameter. -/
theorem not_graphLevelInclusion_of_clique
    {E : Finset (U × U)} (hE : ∀ p ∈ E, p.1 < p.2)
    (R : ℕ) {S : Finset U} (hS : 0 < S.card)
    (hcl : ∀ i ∈ S, ∀ j ∈ S, i < j → (i, j) ∈ E)
    {lam : ℝ} (hlam : lam < (S.card : ℝ) - 1) :
    ¬ GraphLevelInclusion (U := U) (L := {i : U // i ∈ S})
        E R lam := by
  intro hinc
  have hinput :
      matrixLevelPositiveCone (L := {i : U // i ∈ S})
        (graphTwoLayerSpace E) (cliqueLayerWitness S) :=
    ⟨cliqueLayerWitness_mem_matrixLevelSpace hcl,
      cliqueLayerWitness_posSemidef S⟩
  have hout := (hinc (cliqueLayerWitness S) hinput).2
  change
    (graphThetaCliqueOutput E R (lam : ℂ) S).PosSemidef at hout
  have hq :=
    re_qform_nonneg_of_posSemidef hout (cliqueOutputVec S)
  rw [qform_graphThetaCliqueOutput hE hcl] at hq
  have hreal :
      (((S.card : ℂ)
          * ((lam : ℂ) - ((S.card : ℂ) - 1))).re)
        = (S.card : ℝ) * (lam - ((S.card : ℝ) - 1)) := by
    norm_cast
  rw [hreal] at hq
  have hSreal : (0 : ℝ) < S.card := by exact_mod_cast hS
  nlinarith

/-- **Exact protected inclusion at a clique level.**

For an `R`-clique, inclusion of the positive cone in the mapped positivity
locus at the clique's matrix level holds exactly when `λ ≥ R-1`.  This is the
basis-free finite-coordinate content of `eq:exact`. -/
theorem graphCliqueLevelInclusion_iff
    {E : Finset (U × U)} (hE : ∀ p ∈ E, p.1 < p.2)
    {R : ℕ} (hR : 0 < R)
    {S : Finset U} (hSR : S.card = R)
    (hcl : ∀ i ∈ S, ∀ j ∈ S, i < j → (i, j) ∈ E)
    (lam : ℝ) :
    GraphLevelInclusion (U := U) (L := {i : U // i ∈ S})
        E R lam
      ↔ (R : ℝ) - 1 ≤ lam := by
  constructor
  · intro hinc
    by_contra hnot
    have hlt : lam < (R : ℝ) - 1 := lt_of_not_ge hnot
    have hfail :=
      not_graphLevelInclusion_of_clique hE R
        (by simpa [hSR] using hR) hcl
        (lam := lam) (by simpa [hSR] using hlt)
    exact hfail hinc
  · intro hlam
    have hTheta :
        ThetaPositive (graphKraus E) R lam :=
      (thetaPositive_graphKraus_iff hE hR hSR hcl lam).2 hlam
    apply graphLevelInclusion_of_isMapPositiveAt
    apply isMapPositiveAt_graphThetaLinear_of_thetaPositive
      E lam hTheta
    simp [hSR]

/-- At the protected threshold, an `(R+1)`-clique gives failure at the next
matrix level. -/
theorem not_graphCliqueNextLevelInclusion
    {E : Finset (U × U)} (hE : ∀ p ∈ E, p.1 < p.2)
    {R : ℕ}
    {S : Finset U} (hSR : S.card = R + 1)
    (hcl : ∀ i ∈ S, ∀ j ∈ S, i < j → (i, j) ∈ E) :
    ¬ GraphLevelInclusion (U := U) (L := {i : U // i ∈ S})
        E R ((R : ℝ) - 1) := by
  apply not_graphLevelInclusion_of_clique hE R
  · omega
  · exact hcl
  · rw [hSR]
    norm_num

/-- **Exact protected level separation** (`eq:levels`).

If the graph contains an `(R+1)`-clique, the corrected map at `λ=R-1`
induces the positive-cone inclusion at canonical level `Fin n` exactly when
`n ≤ R`. -/
theorem graphProtectedLevelInclusion_iff
    {E : Finset (U × U)} (hE : ∀ p ∈ E, p.1 < p.2)
    {R : ℕ} (hR : 0 < R)
    {S : Finset U} (hSR : S.card = R + 1)
    (hcl : ∀ i ∈ S, ∀ j ∈ S, i < j → (i, j) ∈ E)
    (n : ℕ) :
    GraphLevelInclusion (U := U) (L := Fin n)
        E R ((R : ℝ) - 1)
      ↔ n ≤ R := by
  constructor
  · intro hinc
    by_contra hn
    have hcard :
        Fintype.card {i : U // i ∈ S}
          ≤ Fintype.card (Fin n) := by
      simp only [Fintype.card_coe, Fintype.card_fin, hSR]
      omega
    obtain ⟨e⟩ :=
      Function.Embedding.nonempty_of_card_le hcard
    have hsmall :=
      graphLevelInclusion_of_embedding e hinc
    exact (not_graphCliqueNextLevelInclusion hE hSR hcl) hsmall
  · intro hn
    exact graphLevelInclusion_at_threshold_of_card_le
      hE hR (by simpa using hn)

end GraphInclusion

end RankR
