/-
The explicit level-one lower-bound witness from the higher Choi note.

For a finite coordinate type `T`, the correlated sum of an orthonormal basis
of `so(T)` is

  `K = (d |ω⟩⟨ω| - F) / 2`,

where `d = card T`, `ω` is the normalized diagonal vector, and `F` swaps the
two tensor factors.  The unnormalized diagonal vector used below turns
`d |ω⟩⟨ω|` into `singleOmegaChoi`.
-/
import RankR.HigherChoiSharp

namespace RankR

open Matrix Finset ComplexConjugate
open scoped Kronecker

section Definitions

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- The tensor-factor flip `F(x ⊗ y) = y ⊗ x`. -/
noncomputable def tensorFlip : Matrix (T × T) (T × T) ℂ :=
  Matrix.of fun p q => if p = (q.2, q.1) then 1 else 0

omit [Fintype T] in
@[simp] theorem tensorFlip_apply (p q : T × T) :
    tensorFlip p q = if p = (q.2, q.1) then (1 : ℂ) else 0 := rfl

/-- The all-ordered-pairs rendering of
`∑_{a<b} ((E_ab-E_ba)/√2) ⊗ ((E_ab-E_ba)/√2)`. -/
noncomputable def correlatedSkew :
    Matrix (T × T) (T × T) ℂ :=
  (1 / 4 : ℂ) •
    ∑ p : T × T, skewUnit p.1 p.2 ⊗ₖ skewUnit p.1 p.2

/-- The closed form of the correlated skew sum:
`K = (|Ω⟩⟨Ω| - F)/2 = (d|ω⟩⟨ω| - F)/2`. -/
theorem correlatedSkew_eq :
    correlatedSkew (T := T)
      = (1 / 2 : ℂ) •
          (singleOmegaChoi (T := T) - tensorFlip (T := T)) := by
  ext p q
  have hreal : ∀ a b : T,
      conj (skewUnit a b p.2 q.2) = skewUnit a b p.2 q.2 := by
    intro a b
    rw [skewUnit_apply]
    split_ifs <;> norm_num
  have hsum :
      ∑ x : T × T,
          (skewUnit x.1 x.2 ⊗ₖ skewUnit x.1 x.2) p q
        = 2 * ((if p.1 = p.2 then (1 : ℂ) else 0)
              * (if q.1 = q.2 then 1 else 0)
            - (if p.1 = q.2 then (1 : ℂ) else 0)
              * (if q.1 = p.2 then 1 else 0)) := by
    simp only [Matrix.kroneckerMap_apply]
    conv_lhs =>
      enter [2, x]
      rw [← hreal x.1 x.2]
    exact sum_skewUnit_mul_conj p.1 q.1 p.2 q.2
  rw [correlatedSkew, Matrix.smul_apply, Matrix.sum_apply, hsum,
    Matrix.smul_apply, Matrix.sub_apply]
  simp only [singleOmegaChoi, rankOne, Matrix.of_apply,
    singleOmegaVec_apply, tensorFlip_apply,
    apply_ite (starRingEnd ℂ), map_one, map_zero]
  have hrev : (q.1 = p.2) ↔ (p.2 = q.1) := eq_comm
  simp only [hrev, Prod.ext_iff]
  by_cases hpp : p.1 = p.2
    <;> by_cases hqq : q.1 = q.2
    <;> by_cases hpq : p.1 = q.2
    <;> by_cases hqp : p.2 = q.1
    <;> simp_all
    <;> norm_num

end Definitions

section Computations

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- The unnormalized diagonal vector has squared norm `card T`. -/
theorem norm_sq_singleOmegaVec :
    ‖singleOmegaVec (T := T)‖ ^ 2 = Fintype.card T := by
  rw [norm_sq_eq_sum_normSq, Fintype.sum_prod_type]
  simp [singleOmegaVec_apply, Complex.normSq]

/-- The tensor flip acts by swapping the two coordinates. -/
theorem mulVecE_tensorFlip (x : EuclideanSpace ℂ (T × T)) (p : T × T) :
    mulVecE tensorFlip x p = x (p.2, p.1) := by
  rw [mulVecE_apply]
  have hiff : ∀ q : T × T,
      (p = (q.2, q.1)) ↔ (q = (p.2, p.1)) := by
    intro q
    constructor
    · intro h
      exact Prod.ext (congrArg (fun z => z.2) h).symm
        (congrArg (fun z => z.1) h).symm
    · rintro rfl
      rfl
  simp only [tensorFlip_apply, hiff, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ (p.2, p.1) (fun q => x q)]
  simp

/-- The diagonal vector is fixed by the tensor flip. -/
theorem mulVecE_tensorFlip_singleOmega :
    mulVecE tensorFlip (singleOmegaVec (T := T)) = singleOmegaVec := by
  ext p
  rw [mulVecE_tensorFlip]
  simp [singleOmegaVec_apply, eq_comm]

omit [DecidableEq T] in
/-- A rank-one matrix acts by the corresponding inner product. -/
theorem mulVecE_rankOne_eq (u v x : EuclideanSpace ℂ (T × T)) :
    mulVecE (rankOne u v) x = (inner ℂ v x) • u := by
  ext p
  simp only [mulVecE_apply, rankOne, Matrix.of_apply, PiLp.smul_apply,
    smul_eq_mul, PiLp.inner_apply, RCLike.inner_apply']
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun q _ => by ring

/-- The squared norm of the diagonal vector, in inner-product form. -/
theorem inner_singleOmegaVec_self :
    inner ℂ (singleOmegaVec (T := T)) singleOmegaVec
      = (Fintype.card T : ℂ) := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  have hterm : ∀ p q : T,
      inner ℂ (singleOmegaVec (T := T) (p, q))
          (singleOmegaVec (T := T) (p, q))
        = if p = q then (1 : ℂ) else 0 := by
    intro p q
    by_cases hpq : p = q <;>
      simp [singleOmegaVec_apply, hpq]
  rw [Finset.sum_congr rfl fun p _ =>
    Finset.sum_congr rfl fun q _ => hterm p q]
  simp

/-- The maximally entangled rank-one operator has eigenvalue `card T` on its
diagonal vector. -/
theorem mulVecE_singleOmegaChoi_singleOmega :
    mulVecE (singleOmegaChoi (T := T)) singleOmegaVec
      = (Fintype.card T : ℂ) • singleOmegaVec := by
  rw [singleOmegaChoi, mulVecE_rankOne_eq]
  rw [inner_singleOmegaVec_self]

/-- The correlated skew operator has eigenvalue `(d-1)/2` on the diagonal
vector. -/
theorem mulVecE_correlatedSkew_singleOmega :
    mulVecE (correlatedSkew (T := T)) singleOmegaVec
      = (((Fintype.card T : ℝ) - 1) / 2 : ℂ) • singleOmegaVec := by
  have hsub :
      mulVecE
          (singleOmegaChoi (T := T) - tensorFlip)
          (singleOmegaVec (T := T))
        = mulVecE singleOmegaChoi singleOmegaVec
          - mulVecE tensorFlip singleOmegaVec := by
    ext p
    simp only [mulVecE_apply, Matrix.sub_apply, sub_mul,
      Finset.sum_sub_distrib, PiLp.sub_apply]
  rw [correlatedSkew_eq, smul_mulVecE, hsub,
    mulVecE_singleOmegaChoi_singleOmega,
    mulVecE_tensorFlip_singleOmega]
  ext p
  simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  push_cast
  ring

/-- The full action formula: the correlated skew operator is one half of the
diagonal rank-one operator minus the tensor flip. -/
theorem mulVecE_correlatedSkew (x : EuclideanSpace ℂ (T × T)) :
    mulVecE (correlatedSkew (T := T)) x
      = (1 / 2 : ℂ) •
          ((inner ℂ (singleOmegaVec (T := T)) x) • singleOmegaVec
            - mulVecE tensorFlip x) := by
  have hsub :
      mulVecE
          (singleOmegaChoi (T := T) - tensorFlip)
          x
        = mulVecE singleOmegaChoi x - mulVecE tensorFlip x := by
    ext p
    simp only [mulVecE_apply, Matrix.sub_apply, sub_mul,
      Finset.sum_sub_distrib, PiLp.sub_apply]
  rw [correlatedSkew_eq, smul_mulVecE, hsub,
    singleOmegaChoi, mulVecE_rankOne_eq]

/-- On the flip-symmetric subspace orthogonal to the diagonal vector, the
eigenvalue is `-1/2`. -/
theorem mulVecE_correlatedSkew_of_flip_eq
    {x : EuclideanSpace ℂ (T × T)}
    (horth : inner ℂ (singleOmegaVec (T := T)) x = 0)
    (hflip : mulVecE tensorFlip x = x) :
    mulVecE (correlatedSkew (T := T)) x = (-1 / 2 : ℂ) • x := by
  rw [mulVecE_correlatedSkew, horth, zero_smul, zero_sub, hflip]
  ext p
  simp
  ring

/-- On the flip-antisymmetric subspace, which is automatically orthogonal to
the diagonal vector when the displayed hypothesis is supplied, the eigenvalue
is `1/2`. -/
theorem mulVecE_correlatedSkew_of_flip_eq_neg
    {x : EuclideanSpace ℂ (T × T)}
    (horth : inner ℂ (singleOmegaVec (T := T)) x = 0)
    (hflip : mulVecE tensorFlip x = -x) :
    mulVecE (correlatedSkew (T := T)) x = (1 / 2 : ℂ) • x := by
  rw [mulVecE_correlatedSkew, horth, zero_smul, zero_sub, hflip]
  ext p
  simp

/-- A flip-antisymmetric vector is automatically orthogonal to the diagonal
vector. -/
theorem inner_singleOmegaVec_eq_zero_of_tensorFlip_eq_neg
    {x : EuclideanSpace ℂ (T × T)}
    (hflip : mulVecE tensorFlip x = -x) :
    inner ℂ (singleOmegaVec (T := T)) x = 0 := by
  have hdiag (i : T) : x (i, i) = 0 := by
    have hi := congrArg (fun y => y (i, i)) hflip
    rw [mulVecE_tensorFlip] at hi
    simp only [PiLp.neg_apply] at hi
    linear_combination hi / 2
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  simp [singleOmegaVec_apply, hdiag]

/-- The correlated skew operator has eigenvalue `1/2` on the entire
flip-antisymmetric sector; no separate orthogonality hypothesis is needed. -/
theorem mulVecE_correlatedSkew_of_tensorFlip_eq_neg
    {x : EuclideanSpace ℂ (T × T)}
    (hflip : mulVecE tensorFlip x = -x) :
    mulVecE (correlatedSkew (T := T)) x = (1 / 2 : ℂ) • x :=
  mulVecE_correlatedSkew_of_flip_eq_neg
    (inner_singleOmegaVec_eq_zero_of_tensorFlip_eq_neg hflip) hflip

/-- The three spectral actions used in the level-one witness calculation:
the diagonal line, the symmetric orthogonal sector, and the antisymmetric
sector. -/
theorem correlatedSkew_spectral_actions :
    mulVecE (correlatedSkew (T := T)) singleOmegaVec
        = (((Fintype.card T : ℝ) - 1) / 2 : ℂ) • singleOmegaVec
      ∧
    (∀ x : EuclideanSpace ℂ (T × T),
      inner ℂ (singleOmegaVec (T := T)) x = 0 →
      mulVecE tensorFlip x = x →
      mulVecE correlatedSkew x = (-1 / 2 : ℂ) • x)
      ∧
    (∀ x : EuclideanSpace ℂ (T × T),
      mulVecE tensorFlip x = -x →
      mulVecE correlatedSkew x = (1 / 2 : ℂ) • x) := by
  exact ⟨mulVecE_correlatedSkew_singleOmega,
    fun x => mulVecE_correlatedSkew_of_flip_eq,
    fun x => mulVecE_correlatedSkew_of_tensorFlip_eq_neg⟩

/-- In every dimension at least two the `+1/2` antisymmetric sector is
nonzero.  Thus at dimension two it ties the distinguished diagonal
eigenvalue `(d-1)/2 = 1/2`; that eigenvalue is not simple there. -/
theorem exists_ne_zero_correlatedSkew_half_eigenvector
    (hT : 2 ≤ Fintype.card T) :
    ∃ x : EuclideanSpace ℂ (T × T), x ≠ 0 ∧
      mulVecE (correlatedSkew (T := T)) x = (1 / 2 : ℂ) • x := by
  obtain ⟨i⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card T)
  obtain ⟨j, hji⟩ :=
    Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card T) i
  have hij : i ≠ j := Ne.symm hji
  let x : EuclideanSpace ℂ (T × T) := vec (skewUnit i j)
  have hflip : mulVecE tensorFlip x = -x := by
    ext p
    rw [mulVecE_tensorFlip]
    simp only [x, vec_apply, PiLp.neg_apply]
    rw [skewUnit_apply, skewUnit_apply]
    by_cases hpi : p.1 = i
      <;> by_cases hpj : p.1 = j
      <;> by_cases hqi : p.2 = i
      <;> by_cases hqj : p.2 = j
      <;> simp_all [eq_comm]
  have hx : x ≠ 0 := by
    intro hx
    have hij := congrArg (fun y => y (i, j)) hx
    simp [x, skewUnit, hji] at hij
  exact ⟨x, hx,
    mulVecE_correlatedSkew_of_tensorFlip_eq_neg hflip⟩

/-- The tensor flip is a permutation matrix on `T × T`, so its squared
Hilbert--Schmidt norm is `(card T)^2`. -/
theorem hsNormSq_tensorFlip :
    hsNormSq (tensorFlip (T := T)) = (Fintype.card T : ℝ) ^ 2 := by
  have hrow : ∀ p : T × T,
      ∑ q : T × T, Complex.normSq (tensorFlip p q) = 1 := by
    intro p
    have hiff : ∀ q : T × T,
        (p = (q.2, q.1)) ↔ (q = (p.2, p.1)) := by
      intro q
      constructor
      · intro h
        exact Prod.ext (congrArg (fun z => z.2) h).symm
          (congrArg (fun z => z.1) h).symm
      · rintro rfl
        rfl
    simp only [tensorFlip_apply, hiff]
    have hnorm : ∀ q : T × T,
        Complex.normSq (if q = (p.2, p.1) then (1 : ℂ) else 0)
          = if q = (p.2, p.1) then (1 : ℝ) else 0 := by
      intro q
      by_cases hq : q = (p.2, p.1) <;> simp [hq, Complex.normSq]
    rw [Finset.sum_congr rfl fun q _ => hnorm q]
    rw [Finset.sum_ite_eq' Finset.univ (p.2, p.1)
      (fun _ => (1 : ℝ))]
    simp
  rw [hsNormSq, Finset.sum_congr rfl fun p _ => hrow p,
    Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul]
  push_cast
  ring

/-- The maximally entangled rank-one operator has squared Hilbert--Schmidt
norm `(card T)^2`. -/
theorem hsInner_singleOmegaChoi_self :
    hsInner (singleOmegaChoi (T := T)) singleOmegaChoi
      = ((Fintype.card T : ℝ) ^ 2 : ℂ) := by
  rw [singleOmegaChoi, hsInner_rankOne,
    inner_singleOmegaVec_self]
  simp
  ring

/-- The flip and the maximally entangled rank-one operator have
Hilbert--Schmidt overlap `card T`. -/
theorem hsInner_tensorFlip_singleOmegaChoi :
    hsInner (tensorFlip (T := T)) singleOmegaChoi
      = (Fintype.card T : ℂ) := by
  rw [singleOmegaChoi, hsInner_rankOne_right,
    mulVecE_tensorFlip_singleOmega, inner_singleOmegaVec_self]
  simp

/-- The overlap in the opposite order has the same real value. -/
theorem hsInner_singleOmegaChoi_tensorFlip :
    hsInner (singleOmegaChoi (T := T)) tensorFlip
      = (Fintype.card T : ℂ) := by
  calc
    hsInner (singleOmegaChoi (T := T)) tensorFlip =
        inner ℂ (vec (singleOmegaChoi (T := T)))
          (vec (tensorFlip (T := T))) :=
      hsInner_eq_inner _ _
    _ = conj (inner ℂ (vec (tensorFlip (T := T)))
          (vec (singleOmegaChoi (T := T)))) :=
      (inner_conj_symm (vec (singleOmegaChoi (T := T)))
        (vec (tensorFlip (T := T)))).symm
    _ = conj (hsInner (tensorFlip (T := T))
          (singleOmegaChoi (T := T))) := by
      rw [hsInner_eq_inner]
    _ = (Fintype.card T : ℂ) := by
      rw [hsInner_tensorFlip_singleOmegaChoi]
      simp

/-- The squared Hilbert--Schmidt norm of the correlated skew operator is
`d(d-1)/2`. -/
theorem hsNormSq_correlatedSkew :
    hsNormSq (correlatedSkew (T := T))
      = (Fintype.card T : ℝ) * (Fintype.card T - 1) / 2 := by
  rw [← Complex.ofReal_inj, ← hsInner_self, correlatedSkew_eq,
    hsInner_smul_left, hsInner_smul_right]
  simp only [hsInner_sub_left, hsInner_sub_right]
  rw [
    hsInner_singleOmegaChoi_self,
    hsInner_singleOmegaChoi_tensorFlip,
    hsInner_tensorFlip_singleOmegaChoi,
    hsInner_self, hsNormSq_tensorFlip]
  norm_num [map_inv₀, map_ofNat]
  ring

/-- The correlated skew sum belongs to `so(T) ⊗ so(T)`. -/
theorem correlatedSkew_mem_doubleSkew :
    correlatedSkew (T := T) ∈ doubleSkew T T := by
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro p _
  exact kron_mem_doubleSkew (skewUnit_isSkew _ _) (skewUnit_isSkew _ _)

/-- The exact level-one ratio attained by the correlated skew witness.  This
is the proved lower bound `κ₁ ≥ (d-1)/(2d)`; no upper bound is asserted. -/
theorem correlatedSkew_levelOne_ratio
    (hT : 2 ≤ Fintype.card T) :
    ‖mulVecE (correlatedSkew (T := T)) singleOmegaVec‖ ^ 2
      = ((Fintype.card T : ℝ) - 1) / (2 * Fintype.card T)
          * hsNormSq (correlatedSkew (T := T))
          * ‖singleOmegaVec (T := T)‖ ^ 2 := by
  have hdpos : (0 : ℝ) < Fintype.card T := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hT)
  have hd1 : (1 : ℝ) ≤ Fintype.card T := by
    exact_mod_cast (show 1 ≤ Fintype.card T by omega)
  have hcoef : 0 ≤ ((Fintype.card T : ℝ) - 1) / 2 := by
    linarith
  let c : ℝ := ((Fintype.card T : ℝ) - 1) / 2
  have hc : 0 ≤ c := by simpa [c] using hcoef
  have hnormcoef :
      ‖(c : ℂ)‖ = c := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  have hscalar :
      ((((Fintype.card T : ℝ) : ℂ) - 1) / 2) = (c : ℂ) := by
    dsimp [c]
    push_cast
    ring
  rw [mulVecE_correlatedSkew_singleOmega, norm_smul]
  rw [hscalar, hnormcoef, mul_pow, norm_sq_singleOmegaVec,
    hsNormSq_correlatedSkew]
  field_simp
  dsimp [c]
  ring

omit [DecidableEq T] in
/-- In dimensions at least three, the attained level-one ratio is strictly
larger than the extrapolated value `1/4`. -/
theorem quarter_lt_correlatedSkew_levelOne_ratio
    (hT : 3 ≤ Fintype.card T) :
    (1 / 4 : ℝ)
      < ((Fintype.card T : ℝ) - 1) / (2 * Fintype.card T) := by
  have hd : (3 : ℝ) ≤ Fintype.card T := by exact_mod_cast hT
  have hdpos : (0 : ℝ) < Fintype.card T := by linarith
  rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 4)
    (mul_pos (by norm_num) hdpos)]
  nlinarith

end Computations

end RankR
