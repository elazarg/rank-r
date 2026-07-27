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
    have hd : ∀ c : V, (∑ d, lam a b c d • (skewUnit a b ⊗ₖ skewUnit c d)) x y
        = (∑ d, lam a b c d * skewUnit c d x.2 y.2) * skewUnit a b x.1 y.1 := by
      intro c
      rw [Matrix.sum_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Matrix.smul_apply, Matrix.kroneckerMap_apply, smul_eq_mul]
      ring
    rw [Finset.sum_congr rfl fun c _ => hd c, ← Finset.sum_mul]
    congr 1
    exact sum_mul_skewUnit_apply (fun c d => lam a b c d) x.2 y.2
  rw [skewCombo, Matrix.sum_apply]
  have hmid : ∀ a : U, (∑ b, ∑ c, ∑ d, lam a b c d • (skewUnit a b ⊗ₖ skewUnit c d)) x y
      = ∑ b, (lam a b x.2 y.2 - lam a b y.2 x.2) * skewUnit a b x.1 y.1 := fun a => by
    rw [Matrix.sum_apply]
    exact Finset.sum_congr rfl fun b _ => hinner a b
  rw [Finset.sum_congr rfl fun a _ => hmid a,
    sum_mul_skewUnit_apply (fun a b => lam a b x.2 y.2 - lam a b y.2 x.2) x.1 y.1]
  ring

/-- The alternating four-term sum obeys the Cauchy-Schwarz bound
`|x₁ - x₂ - x₃ + x₄|² ≤ 4 (|x₁|² + |x₂|² + |x₃|² + |x₄|²)`. -/
theorem normSq_sub_sub_add_le (x₁ x₂ x₃ x₄ : ℂ) :
    Complex.normSq (x₁ - x₂ - x₃ + x₄)
      ≤ 4 * (Complex.normSq x₁ + Complex.normSq x₂ + Complex.normSq x₃ + Complex.normSq x₄) := by
  have key : ∀ a b c d : ℝ, (a - b - c + d) * (a - b - c + d)
      ≤ 4 * (a * a + b * b + c * c + d * d) := by
    intro a b c d
    nlinarith [sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a - d), sq_nonneg (b - c),
      sq_nonneg (b + d), sq_nonneg (c + d)]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.sub_re, Complex.add_im, Complex.sub_im]
  have h1 := key x₁.re x₂.re x₃.re x₄.re
  have h2 := key x₁.im x₂.im x₃.im x₄.im
  linarith

omit [DecidableEq U] [DecidableEq V] in
/-- A double sum over `U × V` of a function of the four separated indices unfolds to
the quadruple sum in the order `(U, U, V, V)`. -/
theorem sum_prod_sum_prod (g : U → U → V → V → ℝ) :
    ∑ x : U × V, ∑ y : U × V, g x.1 y.1 x.2 y.2 = ∑ a, ∑ b, ∑ c, ∑ d, g a b c d := by
  simp only [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_comm

/-- The Hilbert-Schmidt norm of a double-skew combination is controlled by the
squared moduli of its coefficients, with constant `16`.

Each entry is an alternating sum of four coefficients, so its squared modulus is at
most `4` times the sum of their squared moduli; each of the four resulting double
sums is the full coefficient sum reindexed by a swap of the `U`-pair, of the
`V`-pair, or of both. -/
theorem hsNormSq_skewCombo_le (lam : U → U → V → V → ℂ) :
    hsNormSq (skewCombo lam)
      ≤ 16 * ∑ a, ∑ b, ∑ c, ∑ d, Complex.normSq (lam a b c d) := by
  have swapU : ∀ f : U → U → V → V → ℝ,
      ∑ a, ∑ b, ∑ c, ∑ d, f b a c d = ∑ a, ∑ b, ∑ c, ∑ d, f a b c d := fun _ => Finset.sum_comm
  have swapV : ∀ f : U → U → V → V → ℝ,
      ∑ a, ∑ b, ∑ c, ∑ d, f a b d c = ∑ a, ∑ b, ∑ c, ∑ d, f a b c d := fun _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  calc hsNormSq (skewCombo lam)
      ≤ ∑ x : U × V, ∑ y : U × V, 4 * (Complex.normSq (lam x.1 y.1 x.2 y.2)
          + Complex.normSq (lam x.1 y.1 y.2 x.2) + Complex.normSq (lam y.1 x.1 x.2 y.2)
          + Complex.normSq (lam y.1 x.1 y.2 x.2)) := by
        refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
        rw [skewCombo_apply]
        exact normSq_sub_sub_add_le _ _ _ _
    _ = 4 * ((∑ x : U × V, ∑ y : U × V, Complex.normSq (lam x.1 y.1 x.2 y.2))
          + (∑ x : U × V, ∑ y : U × V, Complex.normSq (lam x.1 y.1 y.2 x.2))
          + (∑ x : U × V, ∑ y : U × V, Complex.normSq (lam y.1 x.1 x.2 y.2))
          + (∑ x : U × V, ∑ y : U × V, Complex.normSq (lam y.1 x.1 y.2 x.2))) := by
        simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
    _ = 16 * ∑ a, ∑ b, ∑ c, ∑ d, Complex.normSq (lam a b c d) := by
        have h4 : ∑ a, ∑ b, ∑ c, ∑ d, Complex.normSq (lam b a d c)
            = ∑ a, ∑ b, ∑ c, ∑ d, Complex.normSq (lam a b c d) := by
          rw [swapV (fun a b c d => Complex.normSq (lam b a c d)),
            swapU (fun a b c d => Complex.normSq (lam a b c d))]
        rw [sum_prod_sum_prod (fun a b c d => Complex.normSq (lam a b c d)),
          sum_prod_sum_prod (fun a b c d => Complex.normSq (lam a b d c)),
          sum_prod_sum_prod (fun a b c d => Complex.normSq (lam b a c d)),
          sum_prod_sum_prod (fun a b c d => Complex.normSq (lam b a d c)),
          swapV (fun a b c d => Complex.normSq (lam a b c d)),
          swapU (fun a b c d => Complex.normSq (lam a b c d)), h4]
        ring

end SkewCombo

end RankR
