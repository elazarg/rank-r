/-
The Autonne-Takagi interface, and the double-skew action bound derived from it.

This replaces the Fu-Gao-Park estimate as the development's trusted input.  What
is assumed here is Autonne-Takagi: every complex symmetric matrix is `U D Uᵀ`
with `U` unitary and `D` diagonal nonnegative (Horn-Johnson, *Matrix Analysis*,
2nd ed., Cor. 4.4.4(c)).  It is absent from Mathlib, so it is carried as a
`Prop`-valued hypothesis, exactly as `FGPBound` is, and `#print axioms` stays
meaningful.

That hypothesis is **discharged** in `Autonne.lean`, which proves
`Matrix.exists_takagi`; `Results.lean` composes the two, so nothing below
is ultimately assumed.  The separation is kept because it is what makes the
dependency legible: this file is the mathematics, and the interface records
exactly what it needs.

The route to `DoubleSkewBound` follows Fu-Gao-Park's own section 2, but avoids
the two results they import.  Their Theorem 2.4 reaches the bound through a
max-min exchange and the Johnston-Kribs formula for the best Schmidt-rank-two
overlap; neither is needed if one argues on the double-skew subspace directly:

* `K` in the double-skew subspace is symmetric, so Takagi applies:
  `K = ∑ᵢ sᵢ wᵢwᵢᵀ` with `wᵢ` orthonormal.
* For *any* pair `a ≠ b`, the truncation `K₂ = s_a w_aw_aᵀ + s_b w_bw_bᵀ` is
  symmetric and supported on a two-dimensional space, so `⟨K₂, Π K₂⟩ ≤ ½‖K₂‖₂²`.
  That is their Lemma 2.3, which `Flip.lean` reduces to `⟨K₂, K₂^{T_U}⟩ ≥ 0`,
  and the flip trace identity turns that into `(s_a c_a − s_b c_b)² ≥ 0`.
* Since `Π K = K` and `Π` is a self-adjoint idempotent,
  `s_a² + s_b² = ⟨K, K₂⟩ = ⟨K, Π K₂⟩ ≤ ‖K‖₂‖Π K₂‖₂ ≤ ‖K‖₂ √(½(s_a²+s_b²))`;
  cancelling one factor gives `s_a² + s_b² ≤ ½‖K‖₂²` for every pair.
* Finally `KᴴK = ∑ᵢ sᵢ² |w̄ᵢ⟩⟨w̄ᵢ|`, so the action on an orthonormal pair is
  `∑ᵢ sᵢ²θᵢ` with `θᵢ ∈ [0,1]` summing to `2`, and `Weights.lean` bounds that by
  `s_a² + s_b²` for some pair.

No ordering of the `sᵢ` is needed anywhere, because the truncation bound holds
for every pair rather than only for the two largest.
-/
import RankR.SymOuter
import RankR.Weights

namespace RankR

open Matrix Finset ComplexConjugate

/-! ## Private helpers

`hsInner_add_left` and `hsInner_add_right` are in `FGP.lean`; the scalar and
finite-sum cases of sesquilinearity, the linearity of `flipU`, and the two
scalar facts that Lemma 2.3 rests on are only needed here. -/

section Bilinear

variable {W : Type*} [Fintype W]

private theorem hsInner_smul_left (c : ℂ) (A B : Matrix W W ℂ) :
    hsInner (c • A) B = conj c * hsInner A B := by
  simp [hsInner, Matrix.smul_mul]

private theorem hsInner_smul_right (c : ℂ) (A B : Matrix W W ℂ) :
    hsInner A (c • B) = c * hsInner A B := by
  simp [hsInner, Matrix.mul_smul]

private theorem hsInner_sum_left {ι : Type*} [Fintype ι] (A : ι → Matrix W W ℂ)
    (B : Matrix W W ℂ) : hsInner (∑ i, A i) B = ∑ i, hsInner (A i) B := by
  simp [hsInner, Matrix.conjTranspose_sum, Finset.sum_mul, Matrix.trace_sum]

end Bilinear

section FlipLinear

variable {U V : Type*}

private theorem flipU_add (A B : Matrix (U × V) (U × V) ℂ) :
    flipU (A + B) = flipU A + flipU B := by
  ext p q; simp

private theorem flipU_smul (c : ℂ) (A : Matrix (U × V) (U × V) ℂ) :
    flipU (c • A) = c • flipU A := by
  ext p q; simp

end FlipLinear

/-- For a self-adjoint `X`, `Tr (X²) = ⟨X, X⟩ = ‖X‖₂²`. -/
private theorem trace_mul_self_of_conjTranspose_eq {n : Type*} [Fintype n]
    {X : Matrix n n ℂ} (hX : Xᴴ = X) : (X * X).trace = ((hsNormSq X : ℝ) : ℂ) := by
  rw [← hsInner_self]
  show (X * X).trace = (Xᴴ * X).trace
  rw [hX]

/-- The scalar core of Lemma 2.3: `s₁²n₁ + 2s₁s₂t + s₂²n₂ ≥ (s₁√n₁ − s₂√n₂)² ≥ 0`
whenever `|t| ≤ √n₁ √n₂` and the `sᵢ` are nonnegative. -/
private theorem nonneg_of_cross_bound {s₁ s₂ n₁ n₂ t : ℝ} (hs₁ : 0 ≤ s₁) (hs₂ : 0 ≤ s₂)
    (hn₁ : 0 ≤ n₁) (hn₂ : 0 ≤ n₂) (ht : |t| ≤ Real.sqrt n₁ * Real.sqrt n₂) :
    0 ≤ s₁ * s₁ * n₁ + s₁ * s₂ * (2 * t) + s₂ * s₂ * n₂ := by
  have hc₁ : Real.sqrt n₁ ^ 2 = n₁ := Real.sq_sqrt hn₁
  have hc₂ : Real.sqrt n₂ ^ 2 = n₂ := Real.sq_sqrt hn₂
  have ht' : -(Real.sqrt n₁ * Real.sqrt n₂) ≤ t := (abs_le.mp ht).1
  nlinarith [sq_nonneg (s₁ * Real.sqrt n₁ - s₂ * Real.sqrt n₂),
    mul_nonneg (mul_nonneg hs₁ hs₂)
      (by linarith : (0:ℝ) ≤ t + Real.sqrt n₁ * Real.sqrt n₂)]

/-! ## The Autonne-Takagi interface -/

section Interface

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- **Autonne-Takagi factorization**, carried as a hypothesis.

Every complex symmetric matrix factors as `U D Uᵀ` with `U` unitary and `D`
diagonal nonnegative.  Note `Uᵀ`, not `Uᴴ`: that is what distinguishes this from
the spectral theorem, and why the hypothesis is about symmetric rather than
Hermitian matrices. -/
def TakagiFactorization (W : Type*) [Fintype W] [DecidableEq W] : Prop :=
  ∀ K : Matrix W W ℂ, Kᵀ = K →
    ∃ (U : Matrix W W ℂ) (d : W → ℝ),
      U ∈ Matrix.unitaryGroup W ℂ ∧ (∀ i, 0 ≤ d i) ∧
      K = U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᵀ

/-- Takagi in summed form, `K = ∑ᵢ sᵢ wᵢwᵢᵀ` over an orthonormal family.

The `wᵢ` are the columns of `U`, orthonormal because `U` is unitary, and
`(U D Uᵀ) p q = ∑ᵢ dᵢ · U p i · U q i = ∑ᵢ dᵢ · (symOuter wᵢ) p q`. -/
theorem exists_symOuter_decomp (hT : TakagiFactorization W)
    {K : Matrix W W ℂ} (hK : Kᵀ = K) :
    ∃ (s : W → ℝ) (w : W → EuclideanSpace ℂ W),
      (∀ i, 0 ≤ s i) ∧ Orthonormal ℂ w ∧ K = ∑ i, (s i : ℂ) • symOuter (w i) := by
  obtain ⟨Um, d, hUm, hd, hKd⟩ := hT K hK
  refine ⟨d, fun i => WithLp.toLp 2 (fun p => Um p i), hd, ?_, ?_⟩
  · -- the columns of a unitary matrix are orthonormal
    have hstar : Umᴴ * Um = 1 := by
      rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.mp hUm
    refine (orthonormal_iff_ite (𝕜 := ℂ)).mpr fun i j => ?_
    have hcol : (inner ℂ (WithLp.toLp 2 fun p => Um p i) (WithLp.toLp 2 fun p => Um p j) : ℂ)
        = (Umᴴ * Um) i j := by
      rw [PiLp.inner_apply, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun p _ => RCLike.inner_apply' _ _
    rw [hcol, hstar, Matrix.one_apply]
  · rw [hKd]
    ext p q
    rw [Matrix.mul_apply, Matrix.sum_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.smul_apply,
      symOuter_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => by simp [mul_comm, mul_left_comm]

end Interface

/-! ## Lemma 2.3 -/

section PairMat

variable {U V : Type*}

/-- The two-term symmetric matrix that Lemma 2.3 applies to. -/
noncomputable def pairMat (s₁ s₂ : ℝ) (w₁ w₂ : EuclideanSpace ℂ (U × V)) :
    Matrix (U × V) (U × V) ℂ :=
  (s₁ : ℂ) • symOuter w₁ + (s₂ : ℂ) • symOuter w₂

theorem transpose_pairMat (s₁ s₂ : ℝ) (w₁ w₂ : EuclideanSpace ℂ (U × V)) :
    (pairMat s₁ s₂ w₁ w₂)ᵀ = pairMat s₁ s₂ w₁ w₂ := by
  simp [pairMat, Matrix.transpose_add, Matrix.transpose_smul, transpose_symOuter]

end PairMat

section Lemma23

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]

omit [DecidableEq U] [DecidableEq V] in
/-- **Fu-Gao-Park Lemma 2.3**, reduced by `Flip.lean` to a scalar inequality.

Writing `Mᵢ` for the coefficient matrix of `wᵢ` and `cᵢ := ‖MᵢᴴMᵢ‖₂`, the flip
trace identity expands `⟨N, N^{T_U}⟩` as
`s₁² c₁² + 2 s₁ s₂ Re Tr((M₁ᴴM₂)²) + s₂² c₂²`.  By `norm_trace_mul_self_le` and
`hsNormSq_conjTranspose_mul_le` the cross term is at least `−2 s₁ s₂ c₁ c₂`, so
the whole is at least `(s₁c₁ − s₂c₂)² ≥ 0`. -/
theorem hsInner_flipU_pairMat_nonneg {s₁ s₂ : ℝ} (hs₁ : 0 ≤ s₁) (hs₂ : 0 ≤ s₂)
    (w₁ w₂ : EuclideanSpace ℂ (U × V)) :
    0 ≤ (hsInner (pairMat s₁ s₂ w₁ w₂) (flipU (pairMat s₁ s₂ w₁ w₂))).re := by
  -- the diagonal pairings are the squared Hilbert-Schmidt norms of `MᵢᴴMᵢ`
  have hd : ∀ u : EuclideanSpace ℂ (U × V), hsInner (symOuter u) (flipU (symOuter u))
      = ((hsNormSq ((matOf u)ᴴ * matOf u) : ℝ) : ℂ) := fun u => by
    rw [hsInner_symOuter_flipU]
    exact trace_mul_self_of_conjTranspose_eq
      (by rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose])
  -- the two cross pairings are complex conjugates of one another
  have hswap : hsInner (symOuter w₂) (flipU (symOuter w₁))
      = conj (hsInner (symOuter w₁) (flipU (symOuter w₂))) := by
    rw [hsInner_symOuter_flipU, hsInner_symOuter_flipU,
      show (matOf w₂)ᴴ * matOf w₁ = ((matOf w₁)ᴴ * matOf w₂)ᴴ by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose],
      ← Matrix.conjTranspose_mul, Matrix.trace_conjTranspose]
    rfl
  have hTT : hsInner (symOuter w₁) (flipU (symOuter w₂))
      + conj (hsInner (symOuter w₁) (flipU (symOuter w₂)))
      = 2 * ((hsInner (symOuter w₁) (flipU (symOuter w₂))).re : ℂ) := by
    have h := Complex.add_conj (hsInner (symOuter w₁) (flipU (symOuter w₂)))
    push_cast at h
    exact h
  have hexp : hsInner (pairMat s₁ s₂ w₁ w₂) (flipU (pairMat s₁ s₂ w₁ w₂))
      = ((s₁ * s₁ * hsNormSq ((matOf w₁)ᴴ * matOf w₁)
          + s₁ * s₂ * (2 * (hsInner (symOuter w₁) (flipU (symOuter w₂))).re)
          + s₂ * s₂ * hsNormSq ((matOf w₂)ᴴ * matOf w₂) : ℝ) : ℂ) := by
    simp only [pairMat, flipU_add, flipU_smul, hsInner_add_left, hsInner_add_right,
      hsInner_smul_left, hsInner_smul_right, Complex.conj_ofReal, hd, hswap]
    push_cast
    linear_combination ((s₁ : ℂ) * (s₂ : ℂ)) * hTT
  rw [hexp, Complex.ofReal_re]
  refine nonneg_of_cross_bound hs₁ hs₂ (hsNormSq_nonneg _) (hsNormSq_nonneg _) ?_
  calc |(hsInner (symOuter w₁) (flipU (symOuter w₂))).re|
      ≤ ‖hsInner (symOuter w₁) (flipU (symOuter w₂))‖ := Complex.abs_re_le_norm _
    _ ≤ hsNormSq ((matOf w₁)ᴴ * matOf w₂) := by
        rw [hsInner_symOuter_flipU]; exact norm_trace_mul_self_le _
    _ ≤ Real.sqrt (hsNormSq ((matOf w₁)ᴴ * matOf w₁))
          * Real.sqrt (hsNormSq ((matOf w₂)ᴴ * matOf w₂)) :=
        hsNormSq_conjTranspose_mul_le _ _

/-- **Lemma 2.3 in the form the chain consumes**: the double-antisymmetric
quadratic form of a two-term symmetric matrix is at most half its squared
Hilbert-Schmidt norm. -/
theorem qform_Qm_vec_pairMat_le {s₁ s₂ : ℝ} (hs₁ : 0 ≤ s₁) (hs₂ : 0 ≤ s₂)
    (w₁ w₂ : EuclideanSpace ℂ (U × V)) :
    (qform Qm (vec (pairMat s₁ s₂ w₁ w₂))).re ≤ hsNormSq (pairMat s₁ s₂ w₁ w₂) / 2 := by
  rw [qform_Qm_vec_of_transpose_eq (transpose_pairMat s₁ s₂ w₁ w₂)]
  have h := hsInner_flipU_pairMat_nonneg hs₁ hs₂ w₁ w₂
  simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.inv_re,
    Complex.sub_im, Complex.ofReal_im, Complex.inv_im]
  norm_num
  linarith

end Lemma23

/-! ## The truncation chain, and the double-skew bound -/

section Chain

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]

/-- `‖s₁w₁w₁ᵀ + s₂w₂w₂ᵀ‖₂² = s₁² + s₂²` for two distinct members of an
orthonormal family, since the `symOuter` of an orthonormal family is
orthonormal in the Hilbert-Schmidt inner product (`hsInner_symOuter`). -/
theorem hsNormSq_pairMat {s₁ s₂ : ℝ} {w : (U × V) → EuclideanSpace ℂ (U × V)}
    (hw : Orthonormal ℂ w) {a b : U × V} (hab : a ≠ b) :
    hsNormSq (pairMat s₁ s₂ (w a) (w b)) = s₁ ^ 2 + s₂ ^ 2 := by
  have hio := (orthonormal_iff_ite (𝕜 := ℂ)).mp hw
  rw [← Complex.ofReal_inj, ← hsInner_self]
  simp only [pairMat, hsInner_add_left, hsInner_add_right, hsInner_smul_left,
    hsInner_smul_right, hsInner_symOuter, Complex.conj_ofReal, hio a a, hio a b,
    hio b a, hio b b, if_neg hab, if_neg (Ne.symm hab)]
  push_cast
  ring

/-- `⟨K, K₂⟩ = s_a² + s_b²` for the truncation `K₂` of a Takagi decomposition,
again by orthonormality of the `symOuter (w i)`. -/
theorem hsInner_takagi_pairMat {s : (U × V) → ℝ} {w : (U × V) → EuclideanSpace ℂ (U × V)}
    (hw : Orthonormal ℂ w) {a b : U × V} (hab : a ≠ b) :
    hsInner (∑ i, (s i : ℂ) • symOuter (w i)) (pairMat (s a) (s b) (w a) (w b))
      = ((s a ^ 2 + s b ^ 2 : ℝ) : ℂ) := by
  have hio := (orthonormal_iff_ite (𝕜 := ℂ)).mp hw
  have key : ∀ i, hsInner ((s i : ℂ) • symOuter (w i)) (pairMat (s a) (s b) (w a) (w b))
      = (if i = a then ((s a ^ 2 : ℝ) : ℂ) else 0)
        + (if i = b then ((s b ^ 2 : ℝ) : ℂ) else 0) := by
    intro i
    simp only [pairMat, hsInner_add_right, hsInner_smul_left, hsInner_smul_right,
      hsInner_symOuter, Complex.conj_ofReal, hio i a, hio i b]
    split_ifs with h₁ h₂ h₂
    · exact absurd (h₁.symm.trans h₂) hab
    · subst h₁; push_cast; ring
    · subst h₂; push_cast; ring
    · ring
  rw [hsInner_sum_left]
  simp only [key, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ, Finset.mem_univ,
    if_true]
  push_cast
  ring

/-- **The truncation bound.**  For `K` fixed by the double antisymmetrizer, with
Takagi decomposition `∑ᵢ sᵢ wᵢwᵢᵀ`, *every* pair of distinct indices satisfies
`s_a² + s_b² ≤ ½‖K‖₂²`.

This is the square-root-free cancellation, the same move as in
`doubleSkewBound_of_FGP` and `frame_le_of_synthesis_le`: with `A := s_a² + s_b²`,
self-adjointness and idempotence of `Qm` together with `Qm (vec K) = vec K` give
`A = ⟨K, Π K₂⟩ ≤ ‖K‖₂‖Π K₂‖₂`, while Lemma 2.3 gives `‖Π K₂‖₂² ≤ ½A`; squaring
the first and substituting the second yields `A² ≤ ½ A ‖K‖₂²`, and one factor of
`A` cancels. -/
theorem sq_add_sq_le_of_takagi {K : Matrix (U × V) (U × V) ℂ}
    (hK : mulVecE Qm (vec K) = vec K)
    {s : (U × V) → ℝ} (hs : ∀ i, 0 ≤ s i)
    {w : (U × V) → EuclideanSpace ℂ (U × V)} (hw : Orthonormal ℂ w)
    (hdec : K = ∑ i, (s i : ℂ) • symOuter (w i)) {a b : U × V} (hab : a ≠ b) :
    s a ^ 2 + s b ^ 2 ≤ hsNormSq K / 2 := by
  set K₂ := pairMat (s a) (s b) (w a) (w b) with hK₂def
  set A : ℝ := s a ^ 2 + s b ^ 2 with hAdef
  have hA0 : 0 ≤ A := by positivity
  have hnK₂ : hsNormSq K₂ = A := hsNormSq_pairMat hw hab
  have hKK₂ : hsInner K K₂ = (A : ℂ) := by
    rw [hdec, hK₂def]; exact hsInner_takagi_pairMat hw hab
  -- `Qm` is self-adjoint and fixes `vec K`, so it can be moved onto `K₂`
  have hmove : inner ℂ (vec K) (mulVecE Qm (vec K₂)) = (A : ℂ) := by
    rw [inner_mulVecE_left, Qm_conjTranspose, hK, ← hsInner_eq_inner, hKK₂]
  -- Lemma 2.3, applied to the truncation
  have hQ : ‖mulVecE Qm (vec K₂)‖ ^ 2 ≤ A / 2 := by
    rw [norm_mulVecE_Qm_sq]
    have h := qform_Qm_vec_pairMat_le (hs a) (hs b) (w a) (w b)
    rwa [← hK₂def, hnK₂] at h
  -- Cauchy-Schwarz against `vec K`
  have hcs : A ≤ ‖vec K‖ * ‖mulVecE Qm (vec K₂)‖ := by
    have h := norm_inner_le_norm (𝕜 := ℂ) (vec K) (mulVecE Qm (vec K₂))
    rwa [hmove, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA0] at h
  have hKn : ‖vec K‖ ^ 2 = hsNormSq K := (hsNormSq_eq_norm_sq K).symm
  nlinarith [hcs, hQ, hKn, hA0, norm_nonneg (vec K),
    norm_nonneg (mulVecE Qm (vec K₂))]

/-- The action of `K` on a pair of vectors, expanded over a Takagi
decomposition.  By `conjTranspose_symOuter_mul` and orthonormality,
`KᴴK = ∑ᵢ sᵢ² |w̄ᵢ⟩⟨w̄ᵢ|`, so `qform` splits as a weighted sum of `qform_rankOne`
terms. -/
theorem action_eq_sum_weights {s : (U × V) → ℝ}
    {w : (U × V) → EuclideanSpace ℂ (U × V)} (hw : Orthonormal ℂ w)
    {K : Matrix (U × V) (U × V) ℂ} (hdec : K = ∑ i, (s i : ℂ) • symOuter (w i))
    (x y : EuclideanSpace ℂ (U × V)) :
    ‖mulVecE K x‖ ^ 2 + ‖mulVecE K y‖ ^ 2
      = ∑ i, s i ^ 2 * (Complex.normSq (inner ℂ (bar (w i)) x)
          + Complex.normSq (inner ℂ (bar (w i)) y)) := by
  have hio := (orthonormal_iff_ite (𝕜 := ℂ)).mp hw
  have hKK : Kᴴ * K = ∑ i, ((s i ^ 2 : ℝ) : ℂ) • rankOne (bar (w i)) (bar (w i)) := by
    rw [hdec, Matrix.conjTranspose_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_sum, Finset.sum_eq_single i]
    · rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
        conjTranspose_symOuter_mul, hio i i, if_pos rfl, one_smul, smul_smul,
        RCLike.star_def, Complex.conj_ofReal]
      congr 1
      push_cast
      ring
    · intro j _ hji
      rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
        conjTranspose_symOuter_mul, hio i j, if_neg (Ne.symm hji), zero_smul,
        smul_zero, smul_zero]
    · exact fun h => absurd (Finset.mem_univ i) h
  have hq : ∀ z : EuclideanSpace ℂ (U × V), (qform (Kᴴ * K) z).re
      = ∑ i, s i ^ 2 * Complex.normSq (inner ℂ (bar (w i)) z) := by
    intro z
    rw [hKK, qform_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [qform_smul, qform_rankOne, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [norm_mulVecE_sq, norm_mulVecE_sq, hq x, hq y, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

omit [DecidableEq U] [DecidableEq V] in
/-- The weights of `action_eq_sum_weights` lie in `[0,1]`: `θᵢ = ‖P w̄ᵢ‖²` for the
rank-two projection `P` onto `span {x,y}`, and `‖w̄ᵢ‖ = 1`. -/
theorem weights_mem_unit_interval {w : (U × V) → EuclideanSpace ℂ (U × V)}
    (hw : Orthonormal ℂ w) {x y : EuclideanSpace ℂ (U × V)}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : inner ℂ x y = (0 : ℂ)) (i : U × V) :
    Complex.normSq (inner ℂ (bar (w i)) x) + Complex.normSq (inner ℂ (bar (w i)) y) ≤ 1 := by
  have hflip : ∀ z : EuclideanSpace ℂ (U × V),
      Complex.normSq (inner ℂ (bar (w i)) z) = ‖(inner ℂ z (bar (w i)) : ℂ)‖ ^ 2 := fun z => by
    rw [Complex.normSq_eq_norm_sq, ← inner_conj_symm z (bar (w i)), RCLike.norm_conj]
  have hpair : Orthonormal ℂ (![x, y] : Fin 2 → EuclideanSpace ℂ (U × V)) := by
    refine (orthonormal_iff_ite (𝕜 := ℂ)).mpr fun j k => ?_
    have hyx : (inner ℂ y x : ℂ) = 0 := by
      rw [← inner_conj_symm y x, hxy, map_zero]
    fin_cases j <;> fin_cases k <;>
      simp [inner_self_eq_norm_sq_to_K, hx, hy, hxy, hyx]
  have hb : ‖bar (w i)‖ = 1 := (orthonormal_conj hw).1 i
  have hbessel := hpair.sum_inner_products_le (𝕜 := ℂ) (bar (w i)) (s := Finset.univ)
  rw [Fin.sum_univ_two, hb, one_pow] at hbessel
  simpa [hflip] using hbessel

omit [DecidableEq U] [DecidableEq V] in
/-- The weights sum to `2`, because `{w̄ᵢ}` is an orthonormal basis and `x`, `y`
are unit vectors: each of the two Parseval sums contributes `1`. -/
theorem sum_weights_eq_two {w : (U × V) → EuclideanSpace ℂ (U × V)}
    (hw : Orthonormal ℂ w) {x y : EuclideanSpace ℂ (U × V)}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ i, (Complex.normSq (inner ℂ (bar (w i)) x)
      + Complex.normSq (inner ℂ (bar (w i)) y)) = 2 := by
  have hbo : Orthonormal ℂ (fun i => bar (w i)) := orthonormal_conj hw
  rcases isEmpty_or_nonempty (U × V) with hE | hN
  · exfalso; rw [EuclideanSpace.norm_eq] at hx; simp at hx
  -- an orthonormal family of the right cardinality is an orthonormal basis
  obtain ⟨B, hB⟩ : ∃ B : OrthonormalBasis (U × V) ℂ (EuclideanSpace ℂ (U × V)),
      ⇑B = fun i => bar (w i) := by
    have hcard : Fintype.card (U × V) = Module.finrank ℂ (EuclideanSpace ℂ (U × V)) :=
      finrank_euclideanSpace.symm
    have hBcoe : ⇑(basisOfOrthonormalOfCardEqFinrank hbo hcard) = fun i => bar (w i) :=
      coe_basisOfOrthonormalOfCardEqFinrank hbo hcard
    refine ⟨(basisOfOrthonormalOfCardEqFinrank hbo hcard).toOrthonormalBasis
      (by rw [hBcoe]; exact hbo), ?_⟩
    rw [Module.Basis.coe_toOrthonormalBasis]; exact hBcoe
  have parseval : ∀ z : EuclideanSpace ℂ (U × V),
      ∑ i, Complex.normSq (inner ℂ (bar (w i)) z) = ‖z‖ ^ 2 := by
    intro z
    have h := B.sum_sq_norm_inner_right z
    rw [hB] at h
    simpa [Complex.normSq_eq_norm_sq] using h
  rw [Finset.sum_add_distrib, parseval x, parseval y, hx, hy]
  norm_num

/-- **The double-skew action bound, from Autonne-Takagi.**

This is Lemma 2.1 of the manuscript, with `TakagiFactorization` in place of
`FGPBound`: the trusted surface moves from a recent preprint to a classical
factorization theorem. -/
theorem doubleSkewBound_of_takagi (hT : TakagiFactorization (U × V)) :
    DoubleSkewBound U V := by
  intro K hK x y hx hy hxy
  rw [← mulVecE_eq_toEuclideanLin, ← mulVecE_eq_toEuclideanLin]
  obtain ⟨s, w, hs, hw, hdec⟩ :=
    exists_symOuter_decomp hT (transpose_eq_self_of_mem_doubleSkew hK)
  rw [action_eq_sum_weights hw hdec x y]
  obtain ⟨a, b, hab, hle⟩ :=
    exists_pair_sum_weighted_le (fun i => s i ^ 2)
      (fun i => Complex.normSq (inner ℂ (bar (w i)) x)
        + Complex.normSq (inner ℂ (bar (w i)) y))
      (fun i => add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
      (fun i => weights_mem_unit_interval hw hx hy hxy i)
      (sum_weights_eq_two hw hx hy)
  exact hle.trans (sq_add_sq_le_of_takagi (mulVecE_Qm_vec hK) hs hw hdec hab)

end Chain

end RankR
