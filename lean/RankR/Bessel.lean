/-
Two quantitative ingredients that are independent of the rest of the development.

The first is a Bessel-type duality: a uniform bound on the synthesis operator of a
finite family `w` transfers to the same bound on its analysis operator.  The proof
avoids square roots entirely by testing the synthesis bound on the coefficient
vector `c k = ⟪w k, y⟫` itself, for which the pairing `⟪∑ k, c k • w k, y⟫` equals
the real number `∑ k, |c k|²`; Cauchy-Schwarz then yields `S² ≤ (M · S) ‖y‖²`, and
one factor of `S` cancels.

The second is the coefficient bound for the unordered double-skew family.  A linear
combination of the elementary tensors `skewUnit a b ⊗ₖ skewUnit c d` has a closed
entrywise formula: at the position `(x, y)` only the four coefficients obtained from
`(x.1, y.1, x.2, y.2)` by swapping the `U`-pair or the `V`-pair survive, with the
signs of a double antisymmetrization.  Bounding a four-term alternating sum by
`4 ·` the sum of the four squared moduli and reindexing each of the four resulting
sums by the corresponding swap gives the Hilbert-Schmidt bound with constant `16`.
-/
import RankR.Frame

namespace RankR

open Matrix Finset ComplexConjugate
open scoped Kronecker

/-! ## Synthesis bounds imply frame bounds -/

/-- A uniform bound on the synthesis operator of a finite family is inherited by the
analysis operator: if `‖∑ k, c k • w k‖² ≤ M ∑ k |c k|²` for every coefficient
vector `c`, then `∑ k |⟪w k, y⟫|² ≤ M ‖y‖²` for every `y`.

Testing the hypothesis at `c k = ⟪w k, y⟫` makes the synthesized vector `v` pair
with `y` to the real number `S = ∑ k |c k|²`, so `S ≤ ‖v‖ ‖y‖` and therefore
`S² ≤ ‖v‖² ‖y‖² ≤ (M S) ‖y‖²`. -/
theorem frame_le_of_synthesis_le {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (w : ι → E) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ c : ι → ℂ, ‖∑ k, c k • w k‖ ^ 2 ≤ M * ∑ k, Complex.normSq (c k))
    (y : E) :
    ∑ k, Complex.normSq (inner ℂ (w k) y) ≤ M * ‖y‖ ^ 2 := by
  set c : ι → ℂ := fun k => inner ℂ (w k) y with hcdef
  set S : ℝ := ∑ k, Complex.normSq (c k) with hSdef
  set v : E := ∑ k, c k • w k with hvdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => Complex.normSq_nonneg _
  have hinner : (inner ℂ v y : ℂ) = (S : ℂ) := by
    rw [hvdef, sum_inner, hSdef, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [inner_smul_left, Complex.normSq_eq_conj_mul_self, hcdef]
  have hcs : S ≤ ‖v‖ * ‖y‖ := by
    have hle := norm_inner_le_norm (𝕜 := ℂ) v y
    rw [hinner, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS0] at hle
    exact hle
  have hsyn : ‖v‖ ^ 2 ≤ M * S := h c
  have hy0 : (0 : ℝ) ≤ ‖y‖ ^ 2 := sq_nonneg _
  have hsq : S ^ 2 ≤ (M * S) * ‖y‖ ^ 2 := by
    have h1 : S ^ 2 ≤ (‖v‖ * ‖y‖) ^ 2 := by
      have := mul_nonneg (norm_nonneg v) (norm_nonneg y)
      nlinarith
    nlinarith [norm_nonneg v]
  rcases eq_or_lt_of_le hS0 with hz | hpos
  · rw [← hz]
    positivity
  · nlinarith

/-! ## The unordered double-skew family -/

section SkewCombo

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]

/-- Contracting a doubly indexed family against the elementary skew matrices
antisymmetrizes it: `∑_{a,b} f a b (E_{ab} - E_{ba})_{pq} = f p q - f q p`. -/
theorem sum_mul_skewUnit_apply {W : Type*} [Fintype W] [DecidableEq W] (f : W → W → ℂ)
    (p q : W) : ∑ a, ∑ b, f a b * skewUnit a b p q = f p q - f q p := by
  simp [skewUnit, Matrix.single_apply, mul_sub, ite_and, Finset.sum_sub_distrib]

/-- A linear combination of the elementary double-skew tensors
`skewUnit a b ⊗ₖ skewUnit c d` on `U ⊗ V`. -/
noncomputable def skewCombo (lam : U → U → V → V → ℂ) : Matrix (U × V) (U × V) ℂ :=
  ∑ a, ∑ b, ∑ c, ∑ d, lam a b c d • (skewUnit a b ⊗ₖ skewUnit c d)

/-- Entrywise formula for `skewCombo`: at the position `(x, y)` only the four
coefficients obtained from `(x.1, y.1, x.2, y.2)` by swapping the `U`-pair or the
`V`-pair contribute, with the signs of a double antisymmetrization. -/
theorem skewCombo_apply (lam : U → U → V → V → ℂ) (x y : U × V) :
    skewCombo lam x y
      = lam x.1 y.1 x.2 y.2 - lam x.1 y.1 y.2 x.2
        - lam y.1 x.1 x.2 y.2 + lam y.1 x.1 y.2 x.2 := by
  have hinner : ∀ a b : U, (∑ c, ∑ d, lam a b c d • (skewUnit a b ⊗ₖ skewUnit c d)) x y
      = (lam a b x.2 y.2 - lam a b y.2 x.2) * skewUnit a b x.1 y.1 := by
    intro a b
    rw [Matrix.sum_apply]
    have : ∀ c : V, (∑ d, lam a b c d • (skewUnit a b ⊗ₖ skewUnit c d)) x y
        = ∑ d, (lam a b c d * skewUnit c d x.2 y.2) * skewUnit a b x.1 y.1 := by
      intro c
      rw [Matrix.sum_apply]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Matrix.smul_apply, Matrix.kroneckerMap_apply, smul_eq_mul]
      ring
    rw [Finset.sum_congr rfl fun c _ => this c, ← Finset.sum_mul]
    congr 1
    rw [← sum_mul_skewUnit_apply (fun c d => lam a b c d) x.2 y.2]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => rfl
  rw [skewCombo, Matrix.sum_apply]
  have hmid : ∀ a : U, (∑ b, ∑ c, ∑ d, lam a b c d • (skewUnit a b ⊗ₖ skewUnit c d)) x y
      = ∑ b, (lam a b x.2 y.2 - lam a b y.2 x.2) * skewUnit a b x.1 y.1 := fun a => by
    rw [Matrix.sum_apply]
    exact Finset.sum_congr rfl fun b _ => hinner a b
  rw [Finset.sum_congr rfl fun a _ => hmid a,
    sum_mul_skewUnit_apply (fun a b => lam a b x.2 y.2 - lam a b y.2 x.2) x.1 y.1]
  ring

end SkewCombo

end RankR
