/-
Finite-coordinate mixed states and Schmidt-number cones.

The squared norms of the coefficient matrices absorb ensemble weights, so no
separate probability vector is needed.
-/
import RankR.Library.Matrix.Rank
import RankR.Library.Matrix.Action
import RankR.Library.Quantum.BlockPositive
import Mathlib.Analysis.Matrix.Order

namespace RankR

open Matrix Finset ComplexConjugate
open scoped ComplexOrder

variable {W : Type*} [Fintype W]

/-- A finite-coordinate density matrix. -/
def IsDensityMatrix (ρ : Matrix (W × W) (W × W) ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

/-- Mixed-state Schmidt number at most `r`, in the same vectorization
coordinates as `IsBlockPositive`.

The vectors need not be normalized: their squared norms absorb the
nonnegative ensemble weights. -/
def SchmidtNumberLE (r : ℕ) (ρ : Matrix (W × W) (W × W) ℂ) : Prop :=
  ∃ n : ℕ, ∃ C : Fin n → Matrix W W ℂ,
    (∀ i, (C i).rank ≤ r) ∧
      ρ = ∑ i, rankOne (vec (C i)) (vec (C i))

/-- Enlarging the allowed Schmidt rank enlarges the cone. -/
theorem SchmidtNumberLE.mono {r s : ℕ} {ρ : Matrix (W × W) (W × W) ℂ}
    (hρ : SchmidtNumberLE r ρ) (hrs : r ≤ s) :
    SchmidtNumberLE s ρ := by
  obtain ⟨n, C, hCrank, hCsum⟩ := hρ
  exact ⟨n, C, fun i => (hCrank i).trans hrs, hCsum⟩

/-- The Schmidt-number-at-most-`r` cone is closed under addition. -/
theorem SchmidtNumberLE.add {r : ℕ}
    {ρ σ : Matrix (W × W) (W × W) ℂ}
    (hρ : SchmidtNumberLE r ρ) (hσ : SchmidtNumberLE r σ) :
    SchmidtNumberLE r (ρ + σ) := by
  obtain ⟨n, C, hCrank, hCsum⟩ := hρ
  obtain ⟨m, D, hDrank, hDsum⟩ := hσ
  refine ⟨n + m, Fin.append C D, ?_, ?_⟩
  · intro i
    exact Fin.addCases
      (fun j => by simpa using hCrank j)
      (fun j => by simpa using hDrank j) i
  · rw [hCsum, hDsum, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]

/-- The Schmidt-number-at-most-`r` cone is closed under multiplication by a
nonnegative real scalar. -/
theorem SchmidtNumberLE.nonneg_smul {r : ℕ}
    {ρ : Matrix (W × W) (W × W) ℂ}
    [DecidableEq W]
    (hρ : SchmidtNumberLE r ρ) {t : ℝ} (ht : 0 ≤ t) :
    SchmidtNumberLE r ((t : ℂ) • ρ) := by
  obtain ⟨n, C, hCrank, hCsum⟩ := hρ
  let D : Fin n → Matrix W W ℂ :=
    fun i => (Real.sqrt t : ℂ) • C i
  refine ⟨n, D, ?_, ?_⟩
  · intro i
    by_cases ht0 : t = 0
    · subst t
      simp [D]
    · have hsqrt : (Real.sqrt t : ℂ) ≠ 0 := by
        exact_mod_cast Real.sqrt_ne_zero'.mpr
          (lt_of_le_of_ne ht (Ne.symm ht0))
      change (((Real.sqrt t : ℂ) • C i).rank ≤ r)
      rw [rank_smul_eq_of_ne_zero _ hsqrt]
      exact hCrank i
  · rw [hCsum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      ext p q
      simp only [D, vec_smul, PiLp.smul_apply, smul_eq_mul, rankOne,
        Matrix.smul_apply, Matrix.of_apply, map_mul, Complex.conj_ofReal]
      have hsqrt :
          ((Real.sqrt t : ℂ) * (Real.sqrt t : ℂ)) = (t : ℂ) := by
        norm_cast
        simpa [pow_two] using Real.sq_sqrt ht
      rw [← hsqrt]
      ring

/-- The identity on a square bipartite coordinate space has Schmidt number at
most one: its computational-basis decomposition consists of product
projectors. -/
theorem schmidtNumberLE_one
    [DecidableEq W] :
    SchmidtNumberLE 1
      (1 : Matrix (W × W) (W × W) ℂ) := by
  let e : Fin (Fintype.card (W × W)) ≃ W × W :=
    (Fintype.equivFin (W × W)).symm
  let C : Fin (Fintype.card (W × W)) → Matrix W W ℂ :=
    fun a => Matrix.single (e a).1 (e a).2 1
  refine ⟨Fintype.card (W × W), C, ?_, ?_⟩
  · intro a
    let u : W → ℂ := fun i => if i = (e a).1 then 1 else 0
    let v : W → ℂ := fun j => if j = (e a).2 then 1 else 0
    have hsingle : C a = Matrix.vecMulVec u v := by
      ext i j
      simp only [C, u, v, Matrix.single_apply, Matrix.vecMulVec_apply]
      by_cases hi : i = (e a).1 <;> by_cases hj : j = (e a).2 <;>
        simp [hi, hj, eq_comm]
    rw [hsingle]
    exact Matrix.rank_vecMulVec_le u v
  · ext p q
    simp only [Matrix.one_apply, Matrix.sum_apply]
    change (if p = q then 1 else 0) =
      ∑ a, rankOne (vec (C a)) (vec (C a)) p q
    rw [show
      (∑ a, rankOne (vec (C a)) (vec (C a)) p q) =
        ∑ z : W × W,
          rankOne
            (vec (Matrix.single z.1 z.2 (1 : ℂ)))
            (vec (Matrix.single z.1 z.2 (1 : ℂ))) p q by
      simpa only [C] using
        (Equiv.sum_comp e
          (fun z : W × W =>
            rankOne
              (vec (Matrix.single z.1 z.2 (1 : ℂ)))
              (vec (Matrix.single z.1 z.2 (1 : ℂ))) p q))]
    simp only [rankOne, vec_apply, Matrix.single_apply]
    simp_rw [← Prod.ext_iff]
    by_cases hpq : p = q <;> simp [hpq, eq_comm]

/-- Block positivity extends from pure vectors to every positive operator of
Schmidt number at most `r`. -/
theorem re_hsInner_nonneg_of_schmidtNumberLE {r : ℕ}
    {M ρ : Matrix (W × W) (W × W) ℂ}
    (hM : IsBlockPositive r M) (hρ : SchmidtNumberLE r ρ) :
    0 ≤ (hsInner M ρ).re := by
  obtain ⟨n, C, hCrank, rfl⟩ := hρ
  rw [hsInner_sum_right, Complex.re_sum]
  exact Finset.sum_nonneg fun i _ => by
    rw [re_hsInner_rankOne]
    exact hM (C i) (hCrank i)

/-- The expectation of a Hermitian witness is its Hilbert--Schmidt pairing. -/
theorem trace_mul_eq_hsInner_of_isHermitian
    {M ρ : Matrix (W × W) (W × W) ℂ} (hM : M.IsHermitian) :
    (M * ρ).trace = hsInner M ρ := by
  rw [hsInner, hM.eq]

/-- A block-positive Hermitian witness has nonnegative expectation on every
state of Schmidt number at most `r`. -/
theorem trace_mul_nonneg_of_schmidtNumberLE {r : ℕ}
    {M ρ : Matrix (W × W) (W × W) ℂ}
    (hHerm : M.IsHermitian) (hM : IsBlockPositive r M)
    (hρ : SchmidtNumberLE r ρ) :
    0 ≤ ((M * ρ).trace).re := by
  rw [trace_mul_eq_hsInner_of_isHermitian hHerm]
  exact re_hsInner_nonneg_of_schmidtNumberLE hM hρ

end RankR
