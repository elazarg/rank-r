/-
The level-`k` action bound for the double-skew family.

An element `K` of `so(U) ⊗ so(V)` moves an orthonormal *pair* by at most half of
its squared Hilbert-Schmidt norm.  Averaging that pair bound over the `k(k-1)`
ordered pairs drawn from an orthonormal `k`-tuple, in which each index occurs
`k - 1` times, replaces the pair by the tuple:

  `∑_{i < k} ‖K xᵢ‖² ≤ (k/4)‖K‖₂²`.

The averaging needs at least one pair, so the statement is about `k ≥ 2`; at
`k = 1` the constant `1/4` is wrong, an explicit element of `so(3) ⊗ so(3)`
reaching `1/3`.

Bessel's inequality supplies the competing bound `‖K‖₂²`, valid for every
operator and every `k`, and the two combine into `min(k/4, 1)‖K‖₂²`.  Written in
singular values this is `∑_{j ≤ k} s_j(K)² ≤ min{k, 4}/4 · ‖K‖₂²`, the constant
`κ_k` of the higher Choi constants; the action form is what the amplification
argument consumes, and it needs no ordering of the singular values.
-/
import RankR.Equivalence

namespace RankR

open Matrix Finset ComplexConjugate

/-! ## Compression by a projection

Bessel's inequality for the orthonormal tuple, applied one row of `K` at a time. -/

section Compression

variable {W : Type*} [Fintype W]

/-- The conjugate of the `p`-th row of `K`, the vector that pairs with `x` to the
`p`-th coordinate of `K x`. -/
def krow (K : Matrix W W ℂ) (p : W) : EuclideanSpace ℂ W :=
  WithLp.toLp 2 fun q => conj (K p q)

omit [Fintype W] in
@[simp] theorem krow_apply (K : Matrix W W ℂ) (p q : W) : krow K p q = conj (K p q) := rfl

/-- `⟪krow K p, x⟫ = (K x) p`, by construction. -/
theorem inner_krow (K : Matrix W W ℂ) (p : W) (x : EuclideanSpace ℂ W) :
    inner ℂ (krow K p) x = mulVecE K x p := by
  rw [PiLp.inner_apply, mulVecE_apply]
  exact Finset.sum_congr rfl fun q _ => by
    rw [RCLike.inner_apply', krow_apply, Complex.conj_conj]

/-- The rows of `K` carry its whole Hilbert-Schmidt mass. -/
theorem sum_norm_sq_krow (K : Matrix W W ℂ) : ∑ p, ‖krow K p‖ ^ 2 = hsNormSq K :=
  Finset.sum_congr rfl fun p _ => by
    rw [norm_sq_eq_sum_normSq]
    exact Finset.sum_congr rfl fun q _ => by rw [krow_apply, Complex.normSq_conj]

/-- **Compressing by a projection does not increase the Hilbert-Schmidt norm.**
For any operator and any orthonormal tuple, of any length,

  `∑ᵢ ‖K xᵢ‖² ≤ ‖K‖₂²`.

Coordinatewise this is Bessel's inequality for the tuple, applied to the
conjugate row `krow K p` and summed over `p`. -/
theorem sum_norm_sq_le_hsNormSq (K : Matrix W W ℂ) {k : ℕ}
    (x : Fin k → EuclideanSpace ℂ W) (hx : Orthonormal ℂ x) :
    ∑ i, ‖mulVecE K (x i)‖ ^ 2 ≤ hsNormSq K := by
  have hrow : ∀ i : Fin k,
      ‖mulVecE K (x i)‖ ^ 2 = ∑ p, ‖inner ℂ (x i) (krow K p)‖ ^ 2 := fun i => by
    rw [norm_sq_eq_sum_normSq]
    exact Finset.sum_congr rfl fun p _ => by
      rw [← inner_krow, ← inner_conj_symm, Complex.normSq_conj, Complex.normSq_eq_norm_sq]
  rw [Finset.sum_congr rfl fun i _ => hrow i, Finset.sum_comm, ← sum_norm_sq_krow K]
  exact Finset.sum_le_sum fun p _ => hx.sum_inner_products_le (krow K p)

end Compression

/-! ## The averaged pair bound -/

section DoubleSkew

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]

/-- Removing the diagonal from a double sum over `Fin k` subtracts the diagonal
terms, one for each index. -/
theorem sum_sum_ite_ne (k : ℕ) (f : Fin k → Fin k → ℝ) :
    ∑ i : Fin k, ∑ j : Fin k, (if i ≠ j then f i j else 0)
      = (∑ i : Fin k, ∑ j : Fin k, f i j) - ∑ i : Fin k, f i i := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : ∀ j : Fin k, (if i ≠ j then f i j else 0) = f i j - (if i = j then f i j else 0) :=
    fun j => by by_cases h : i = j <;> simp [h]
  rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_sub_distrib, Finset.sum_ite_eq]
  simp

/-- **The level-`k` action bound.**  For `K` fixed by the double antisymmetrizer
and any orthonormal `k`-tuple with `k ≥ 2`,

  `∑ᵢ ‖K xᵢ‖² ≤ (k/4)‖K‖₂²`.

The double-skew bound applied to the pair `(xᵢ, xⱼ)` for `i ≠ j` gives
`‖K xᵢ‖² + ‖K xⱼ‖² ≤ ½‖K‖₂²`.  Summing over the `k(k - 1)` ordered pairs, in each
of which every index occurs `k - 1` times, gives
`2(k - 1)∑ᵢ‖K xᵢ‖² ≤ k(k - 1)·½‖K‖₂²`, and `k ≥ 2` makes `k - 1` cancellable.

The hypothesis `k ≥ 2` is the whole content of the averaging: it guarantees that
at least one pair exists.  At `k = 1` the conclusion is false — the element
`∑_α L_α ⊗ L_α` of `so(3) ⊗ so(3)` has `s₁² / ‖·‖₂² = 1/3`. -/
theorem sum_norm_sq_le_of_doubleSkewQm (hDS : DoubleSkewBoundQm U V)
    {K : Matrix (U × V) (U × V) ℂ} (hK : mulVecE Qm (vec K) = vec K)
    {k : ℕ} (hk : 2 ≤ k) (x : Fin k → EuclideanSpace ℂ (U × V)) (hx : Orthonormal ℂ x) :
    ∑ i, ‖mulVecE K (x i)‖ ^ 2 ≤ (k / 4 : ℝ) * hsNormSq K := by
  set a : Fin k → ℝ := fun i => ‖mulVecE K (x i)‖ ^ 2 with ha
  set S : ℝ := ∑ i, a i with hS
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  -- the pair bound, on every ordered off-diagonal pair
  have hpair : ∀ i j : Fin k, i ≠ j → a i + a j ≤ hsNormSq K / 2 :=
    fun i j hij => hDS K hK (x i) (x j) (hx.1 i) (hx.1 j) (hx.2 hij)
  have hle : ∑ i : Fin k, ∑ j : Fin k, (if i ≠ j then a i + a j else 0)
      ≤ ∑ i : Fin k, ∑ j : Fin k, (if i ≠ j then hsNormSq K / 2 else 0) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
      by_cases h : i ≠ j
      · simpa [h] using hpair i j h
      · simp [h]
  -- each index occurs in `k - 1` ordered pairs
  have hL : ∑ i : Fin k, ∑ j : Fin k, (if i ≠ j then a i + a j else 0)
      = ((k : ℝ) - 1) * (2 * S) := by
    rw [sum_sum_ite_ne]
    have h1 : ∀ i : Fin k, ∑ j : Fin k, (a i + a j) = (k : ℝ) * a i + S := fun i => by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, hS]
    rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← hS]
    have h2 : ∑ i : Fin k, (a i + a i) = 2 * S := by
      rw [Finset.sum_add_distrib, ← hS]; ring
    rw [h2]; ring
  have hR : ∑ i : Fin k, ∑ j : Fin k, (if i ≠ j then hsNormSq K / 2 else 0)
      = ((k : ℝ) - 1) * ((k : ℝ) * (hsNormSq K / 2)) := by
    rw [sum_sum_ite_ne]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hL, hR] at hle
  have hcancel : 2 * S ≤ (k : ℝ) * (hsNormSq K / 2) := le_of_mul_le_mul_left hle hk1
  linarith

/-- **The level-`k` action bound and the trivial bound together.**  The constant
is `min(k/4, 1)`, which is `κ_k = min{k, 4}/4`: the averaged pair bound governs
`k ≤ 4` and the Hilbert-Schmidt norm governs the rest. -/
theorem sum_norm_sq_le_min_of_doubleSkewQm (hDS : DoubleSkewBoundQm U V)
    {K : Matrix (U × V) (U × V) ℂ} (hK : mulVecE Qm (vec K) = vec K)
    {k : ℕ} (hk : 2 ≤ k) (x : Fin k → EuclideanSpace ℂ (U × V)) (hx : Orthonormal ℂ x) :
    ∑ i, ‖mulVecE K (x i)‖ ^ 2 ≤ min ((k : ℝ) / 4) 1 * hsNormSq K := by
  rcases le_total ((k : ℝ) / 4) 1 with h | h
  · rw [min_eq_left h]
    exact sum_norm_sq_le_of_doubleSkewQm hDS hK hk x hx
  · rw [min_eq_right h, one_mul]
    exact sum_norm_sq_le_hsNormSq K x hx

end DoubleSkew

end RankR
