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
    rw [EuclideanSpace.norm_sq_eq]
    simp_rw [← Complex.normSq_eq_norm_sq]
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
    rw [EuclideanSpace.norm_sq_eq]
    simp_rw [← Complex.normSq_eq_norm_sq]
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
`‖K xᵢ‖² + ‖K xⱼ‖² ≤ ½‖K‖₂²`.  Summing over the `k(k - 1)` ordered pairs, in
each of which every index occurs `k - 1` times, gives
`2(k - 1)∑ᵢ‖K xᵢ‖² ≤ k(k - 1)·½‖K‖₂²`, and `k ≥ 2` makes `k - 1`
cancellable.

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

/-- Projection duality at exact matrix rank `k ≥ 2`: the level-`k` action
bound for the range of `Qm` gives the same `min(k/4,1)` bound on the
Frobenius norm of the projection of a rank-`k` matrix. -/
theorem hsNormSq_dsProj_le_min_of_rank_eq
    (hDS : DoubleSkewBoundQm U V)
    (M : Matrix (U × V) (U × V) ℂ) {k : ℕ}
    (hk : 2 ≤ k) (hrank : M.rank = k) :
    hsNormSq (dsProj M) ≤ min ((k : ℝ) / 4) 1 * hsNormSq M := by
  have hA0 : 0 ≤ hsNormSq (dsProj M) := hsNormSq_nonneg _
  have hB0 : 0 ≤ hsNormSq M := hsNormSq_nonneg M
  have hcoef0 : 0 ≤ min ((k : ℝ) / 4) 1 :=
    le_min (by positivity) (by norm_num)
  have hvK : vec (dsProj M) = mulVecE Qm (vec M) := vec_dsProj M
  have hfix : mulVecE Qm (vec (dsProj M)) = vec (dsProj M) := by
    rw [hvK, mulVecE_mul, Qm_mul_self]
  have hb : ((hsNormSq (dsProj M) : ℝ) : ℂ) = hsInner (dsProj M) M := by
    rw [← hsInner_self, hsInner_eq_inner, hsInner_eq_inner]
    nth_rewrite 2 [hvK]
    rw [inner_mulVecE_left, Qm_conjTranspose, hfix]
  obtain ⟨n, hn, e, d, he, hMeq, hdM⟩ :
      ∃ n : ℕ, n = k ∧ ∃ e d : Fin n → EuclideanSpace ℂ (U × V),
        Orthonormal ℂ e ∧ M = ∑ i, rankOne (d i) (e i) ∧
          ∑ i, ‖d i‖ ^ 2 = hsNormSq M := by
    obtain ⟨n, e₀, d₀, he₀, hMT, hn⟩ :
        ∃ n : ℕ, ∃ e d : Fin n → EuclideanSpace ℂ (U × V),
          Orthonormal ℂ e ∧ Mᵀ = rankFactor e d ∧ n = k := by
      obtain ⟨e₀, d₀, he₀, hMT⟩ := exists_rankFactor_rank Mᵀ
      exact ⟨Mᵀ.rank, e₀, d₀, he₀, hMT,
        by simpa only [Matrix.rank_transpose] using hrank⟩
    refine ⟨n, hn, fun i => bar (e₀ i), fun i => bar (d₀ i),
      orthonormal_conj he₀, ?_, ?_⟩
    · have h : (Mᵀ)ᵀ = (rankFactor e₀ d₀)ᵀ := congrArg (·ᵀ) hMT
      rw [Matrix.transpose_transpose, rankFactor_eq_sum,
        Matrix.transpose_sum] at h
      exact h.trans
        (Finset.sum_congr rfl fun i _ => transpose_rankOne _ _)
    · rw [← hsNormSq_transpose M, hMT,
        hsNormSq_rankFactor_eq e₀ d₀ he₀]
      exact Finset.sum_congr rfl fun i _ => by rw [norm_bar]
  subst n
  have hterm : ∀ i, ‖hsInner (dsProj M) (rankOne (d i) (e i))‖
      ≤ ‖d i‖ * ‖mulVecE (dsProj M) (e i)‖ := fun i => by
    rw [hsInner_rankOne_right, RCLike.norm_conj]
    exact norm_inner_le_norm _ _
  have hsum : hsNormSq (dsProj M)
      ≤ ∑ i, ‖d i‖ * ‖mulVecE (dsProj M) (e i)‖ := by
    have h0 : ((hsNormSq (dsProj M) : ℝ) : ℂ)
        = ∑ i, hsInner (dsProj M) (rankOne (d i) (e i)) := by
      rw [hb, ← hsInner_sum_right, ← hMeq]
    calc
      hsNormSq (dsProj M) =
          ‖((hsNormSq (dsProj M) : ℝ) : ℂ)‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA0]
      _ = ‖∑ i, hsInner (dsProj M) (rankOne (d i) (e i))‖ := by
        rw [h0]
      _ ≤ ∑ i, ‖hsInner (dsProj M) (rankOne (d i) (e i))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i, ‖d i‖ * ‖mulVecE (dsProj M) (e i)‖ :=
        Finset.sum_le_sum fun i _ => hterm i
  have hcs : ∑ i, ‖d i‖ * ‖mulVecE (dsProj M) (e i)‖
      ≤ Real.sqrt (∑ i, ‖d i‖ ^ 2)
        * Real.sqrt (∑ i, ‖mulVecE (dsProj M) (e i)‖ ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  rw [hdM] at hcs
  have hS :
      ∑ i, ‖mulVecE (dsProj M) (e i)‖ ^ 2
        ≤ min ((k : ℝ) / 4) 1 * hsNormSq (dsProj M) := by
    exact sum_norm_sq_le_min_of_doubleSkewQm hDS hfix hk e he
  have hSnn : (0 : ℝ) ≤
      ∑ i, ‖mulVecE (dsProj M) (e i)‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hAsq : hsNormSq (dsProj M) ^ 2
      ≤ hsNormSq M *
        ∑ i, ‖mulVecE (dsProj M) (e i)‖ ^ 2 := by
    have h2 := mul_self_le_mul_self hA0 (hsum.trans hcs)
    rw [← Real.sq_sqrt hB0, ← Real.sq_sqrt hSnn]
    nlinarith [h2]
  have hBS :
      hsNormSq M * (∑ i, ‖mulVecE (dsProj M) (e i)‖ ^ 2)
        ≤ hsNormSq M *
          (min ((k : ℝ) / 4) 1 * hsNormSq (dsProj M)) :=
    mul_le_mul_of_nonneg_left hS hB0
  by_cases hAzero : hsNormSq (dsProj M) = 0
  · rw [hAzero]
    positivity
  · have hApos : 0 < hsNormSq (dsProj M) :=
      lt_of_le_of_ne hA0 (Ne.symm hAzero)
    have hmul :
        hsNormSq (dsProj M) *
            hsNormSq (dsProj M) ≤
          hsNormSq (dsProj M) *
            (min ((k : ℝ) / 4) 1 * hsNormSq M) := by
      calc
        hsNormSq (dsProj M) * hsNormSq (dsProj M) =
            hsNormSq (dsProj M) ^ 2 := by ring
        _ ≤ hsNormSq M *
            (∑ i, ‖mulVecE (dsProj M) (e i)‖ ^ 2) := hAsq
        _ ≤ hsNormSq M *
            (min ((k : ℝ) / 4) 1 * hsNormSq (dsProj M)) := hBS
        _ = hsNormSq (dsProj M) *
            (min ((k : ℝ) / 4) 1 * hsNormSq M) := by ring
    exact le_of_mul_le_mul_left hmul hApos

/-- Projection duality for every rank-at-most-`k` matrix, including ranks
zero and one. -/
theorem hsNormSq_dsProj_le_min (hDS : DoubleSkewBoundQm U V)
    (M : Matrix (U × V) (U × V) ℂ) {k : ℕ}
    (hk : 2 ≤ k) (hrank : M.rank ≤ k) :
    hsNormSq (dsProj M) ≤ min ((k : ℝ) / 4) 1 * hsNormSq M := by
  by_cases hMrank : 2 ≤ M.rank
  · have hexact :=
      hsNormSq_dsProj_le_min_of_rank_eq hDS M hMrank rfl
    have hcast : (M.rank : ℝ) ≤ k := by exact_mod_cast hrank
    have hcoef :
        min ((M.rank : ℝ) / 4) 1 ≤ min ((k : ℝ) / 4) 1 := by
      gcongr
    exact hexact.trans
      (mul_le_mul_of_nonneg_right hcoef (hsNormSq_nonneg M))
  · have htwo : M.rank ≤ 2 := by omega
    have hhalf : (1 / 2 : ℝ) ≤ min ((k : ℝ) / 4) 1 := by
      apply le_min
      · have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
        linarith
      · norm_num
    calc
      hsNormSq (dsProj M) ≤ (1 / 2 : ℝ) * hsNormSq M := by
        simpa [div_eq_mul_inv, mul_comm] using
          hsNormSq_dsProj_le hDS M htwo
      _ ≤ min ((k : ℝ) / 4) 1 * hsNormSq M :=
        mul_le_mul_of_nonneg_right hhalf (hsNormSq_nonneg M)

/-- The double antisymmetrizer has level-`k` quadratic-form norm at most
`min(k/4,1)` on matrices of rank at most `k`. -/
theorem qform_Qm_rank_le_min (C : Matrix (U × V) (U × V) ℂ)
    {k : ℕ} (hk : 2 ≤ k) (hrank : C.rank ≤ k) :
    (qform Qm (vec C)).re ≤ min ((k : ℝ) / 4) 1 * hsNormSq C := by
  rw [← norm_mulVecE_Qm_sq, ← vec_dsProj, ← hsNormSq_eq_norm_sq]
  exact hsNormSq_dsProj_le_min doubleSkewBoundQm_holds C hk hrank

/-- The level-`k` Choi bound for the double antisymmetrizer, in the
normalization intrinsic to `Qm`. -/
theorem choiKBound_Qm_min {k : ℕ} (hk : 2 ≤ k) :
    ChoiKBound
      (Qm : Matrix (Idx U V) (Idx U V) ℂ)
      k (min ((k : ℝ) / 4) 1 / k) := by
  intro u v
  let C : Matrix (U × V) (U × V) ℂ :=
    ∑ i, rankOne (u i) (v i)
  have hCrank : C.rank ≤ k :=
    (rank_le_iff_exists_sum_rankOne C).mpr ⟨u, v, rfl⟩
  have hq := qform_Qm_rank_le_min C hk hCrank
  have hkR : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hk)
  calc
    (qform Qm (vec (∑ i, rankOne (u i) (v i)))).re =
        (qform Qm (vec C)).re := rfl
    _ ≤ min ((k : ℝ) / 4) 1 * hsNormSq C := hq
    _ = (k : ℝ) * (min ((k : ℝ) / 4) 1 / k) * hsNormSq C := by
      field_simp [ne_of_gt hkR]

/-- Rescaling `Qm` to the manuscript's Choi normalization gives the stated
upper constant `min(1,4/k)` for every `k ≥ 2`. -/
theorem choiKBound_four_smul_Qm_min {k : ℕ} (hk : 2 ≤ k) :
    ChoiKBound
      ((4 : ℂ) • (Qm : Matrix (Idx U V) (Idx U V) ℂ))
      k (min 1 (4 / (k : ℝ))) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hk)
  have hβ :
      4 * (min ((k : ℝ) / 4) 1 / k) = min 1 (4 / (k : ℝ)) := by
    by_cases hkle : (k : ℝ) / 4 ≤ 1
    · have hone : (1 : ℝ) ≤ 4 / k := by
        rw [le_div_iff₀ hkR]
        linarith
      rw [min_eq_left hkle, min_eq_left hone]
      field_simp [ne_of_gt hkR]
    · have hone : (1 : ℝ) ≤ (k : ℝ) / 4 := le_of_not_ge hkle
      have hfour : 4 / (k : ℝ) ≤ 1 := by
        rw [div_le_one hkR]
        linarith
      rw [min_eq_right hone, min_eq_right hfour]
      ring
  rw [← hβ]
  exact choiKBound_smul (by norm_num) (choiKBound_Qm_min hk)

end DoubleSkew

end RankR
