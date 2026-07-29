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

end RankOne

end RankR
