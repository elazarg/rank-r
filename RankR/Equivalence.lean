/-
The converse direction: the Fu-Gao-Park estimate itself, proved.

`FGP.lean` shows `FGPBound → DoubleSkewBound`.  This file supplies the converse
and therefore, composed with `Takagi.lean`, a proof of `FGPBound` — that is, of
Fu-Gao-Park's Theorem 2.4 in the rendering `Conventions.lean` fixes.

The obstacle to the converse is a mismatch of hypotheses, not mathematics.
`DoubleSkewBound` quantifies over `K ∈ doubleSkew U V`, the *span* of the
elementary tensors `L ⊗ M`, whereas the converse naturally produces
`K := dsProj M`, for which what is known is `Qm (vec K) = vec K`.  Bridging
those needs `ran Qm ⊆ vec (doubleSkew U V)`, a spanning argument requiring a
linear order on `U` and `V`.

It is avoided entirely by restating the bound with the fixed-point hypothesis.
`DoubleSkewBoundQm` is formally *stronger* than `DoubleSkewBound` — it applies
to more `K` — but it is no harder to prove, because everything the argument of
`Takagi.lean` needs is derivable from `Qm (vec K) = vec K`: that hypothesis
already forces `Kᵀ = K`, by `transpose_eq_self_of_Qm_fixed` below.
-/
import RankR.Autonne
import RankR.Takagi
import RankR.FGP

namespace RankR

open Matrix Finset ComplexConjugate

section Interface

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- **Autonne-Takagi holds**, so the hypothesis carried through `Takagi.lean` is
discharged.  This is `Matrix.exists_takagi` repackaged as the `Prop` that file
assumes. -/
theorem takagiFactorization_holds : TakagiFactorization W :=
  fun _K hK => Matrix.exists_takagi _K hK

end Interface

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]

/-! ## The double-skew projection at the level of matrices -/

/-- The orthogonal projection of `L(U ⊗ V)` onto `so(U) ⊗ so(V)`, written with
the partial transposes of `Flip.lean` rather than through `vec`.  This is `Qm`
transported along `vec`; see `vec_dsProj`. -/
noncomputable def dsProj (M : Matrix (U × V) (U × V) ℂ) : Matrix (U × V) (U × V) ℂ :=
  (4 : ℂ)⁻¹ • (M - flipU M - flipV M + Mᵀ)

/-- `dsProj` is `Qm` conjugated by `vec`. -/
theorem vec_dsProj (M : Matrix (U × V) (U × V) ℂ) :
    vec (dsProj M) = mulVecE Qm (vec M) := by
  ext X
  rw [mulVecE_Qm]
  show ((4 : ℂ)⁻¹ • (M - flipU M - flipV M + Mᵀ)) X.1 X.2 = _
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
  rfl

/-! ## The fixed-point form of the double-skew bound -/

/-- The double-skew action bound, with `K` required only to be fixed by the
double antisymmetrizer rather than to lie in the span of the elementary
tensors.

`mulVecE_Qm_vec` shows `doubleSkew U V` is contained in the fixed set, so this
implies `DoubleSkewBound`; the reverse containment is not proved anywhere in the
development and is not needed. -/
def DoubleSkewBoundQm (U V : Type*)
    [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] : Prop :=
  ∀ K : Matrix (U × V) (U × V) ℂ, mulVecE Qm (vec K) = vec K →
    ∀ x y : EuclideanSpace ℂ (U × V),
      ‖x‖ = 1 → ‖y‖ = 1 → inner ℂ x y = 0 →
        ‖mulVecE K x‖ ^ 2 + ‖mulVecE K y‖ ^ 2 ≤ hsNormSq K / 2

/-- A matrix fixed by the double antisymmetrizer is symmetric.

Writing `f = vec K`, the fixed-point equation at `X` reads
`f X − f (swU X) − f (swV X) + f (swV (swU X)) = 4 f X`.  Adding it to the same
equation at `swU X` gives `f (swU X) = −f X`, and at `swV X` gives
`f (swV X) = −f X`; substituting back gives `f (swV (swU X)) = f X`, which is
`Kᵀ = K`. -/
theorem transpose_eq_self_of_Qm_fixed {K : Matrix (U × V) (U × V) ℂ}
    (hK : mulVecE Qm (vec K) = vec K) : Kᵀ = K := by
  have key : ∀ X : Idx U V, (4 : ℂ)⁻¹ * (vec K X - vec K (swU X) - vec K (swV X)
      + vec K (swV (swU X))) = vec K X := by
    intro X
    rw [← mulVecE_Qm]
    exact congrFun (congrArg WithLp.ofLp hK) X
  ext p q
  have h1 := key ((p, q) : Idx U V)
  have h2 := key (swU ((p, q) : Idx U V))
  have h3 := key (swV ((p, q) : Idx U V))
  simp only [swU_swU, swV_swV, swU_swV] at h2 h3
  have hd : vec K (swV (swU ((p, q) : Idx U V))) = vec K ((p, q) : Idx U V) := by
    linear_combination 2 * h1 - h2 - h3
  exact hd

/-- The fixed-point form implies the span form. -/
theorem doubleSkewBound_of_Qm (h : DoubleSkewBoundQm U V) : DoubleSkewBound U V := by
  intro K hK x y hx hy hxy
  rw [← mulVecE_eq_toEuclideanLin, ← mulVecE_eq_toEuclideanLin]
  exact h K (mulVecE_Qm_vec hK) x y hx hy hxy

/-- **The double-skew bound in fixed-point form, from Autonne-Takagi.**  The
proof of `doubleSkewBound_of_takagi` used `K ∈ doubleSkew U V` only through
`transpose_eq_self_of_mem_doubleSkew` and `mulVecE_Qm_vec`; both are available
here, the first by `transpose_eq_self_of_Qm_fixed` and the second by
hypothesis. -/
theorem doubleSkewBoundQm_of_takagi (hT : TakagiFactorization (U × V)) :
    DoubleSkewBoundQm U V := by
  intro K hK x y hx hy hxy
  obtain ⟨s, w, hs, hw, hdec⟩ :=
    exists_symOuter_decomp hT (transpose_eq_self_of_Qm_fixed hK)
  rw [action_eq_sum_weights hw hdec x y]
  obtain ⟨a, b, hab, hle⟩ :=
    exists_pair_sum_weighted_le (fun i => s i ^ 2)
      (fun i => Complex.normSq (inner ℂ (bar (w i)) x)
        + Complex.normSq (inner ℂ (bar (w i)) y))
      (fun i => add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
      (fun i => weights_mem_unit_interval hw hx hy hxy i)
      (sum_weights_eq_two hw hx hy)
  exact hle.trans (sq_add_sq_le_of_takagi hK hs hw hdec hab)

/-- **The double-skew bound in fixed-point form**, unconditionally. -/
theorem doubleSkewBoundQm_holds : DoubleSkewBoundQm U V :=
  doubleSkewBoundQm_of_takagi takagiFactorization_holds

/-- **The double-skew action bound** (`lem:double-skew`), unconditionally. -/
theorem doubleSkewBound_holds : DoubleSkewBound U V :=
  doubleSkewBound_of_Qm doubleSkewBoundQm_holds

/-! ## The converse -/

/-- Pairing against a rank-one operator is the vector pairing against the action:
both sides expand to `∑_{p,q} conj (A q p) · x q · conj (y p)`. -/
theorem hsInner_rankOne_right {W : Type*} [Fintype W] (A : Matrix W W ℂ)
    (x y : EuclideanSpace ℂ W) :
    hsInner A (rankOne x y) = conj (inner ℂ x (mulVecE A y)) := by
  simp only [hsInner, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, RCLike.star_def, rankOne, Matrix.of_apply,
    PiLp.inner_apply, RCLike.inner_apply', mulVecE_apply, map_sum, map_mul,
    Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by ring

/-- Transposition preserves the rank.  `Matrix.rank_transpose` needs only
`Field`, whereas `Matrix.rank_conjTranspose` lives in a `StarOrderedField`
section and would require the star order on `ℂ`; the development orders `ℂ`
nowhere, so the transpose is used throughout. -/
theorem rank_transpose_le {W : Type*} [Fintype W]
    {A : Matrix W W ℂ} {k : ℕ} (h : A.rank ≤ k) : Aᵀ.rank ≤ k := by
  rwa [Matrix.rank_transpose]

/-- `(|x⟩⟨y|)ᵀ = |ȳ⟩⟨x̄|`. -/
theorem transpose_rankOne {W : Type*} (x y : EuclideanSpace ℂ W) :
    (rankOne x y)ᵀ = rankOne (bar y) (bar x) := by
  ext p q
  simp [rankOne, Matrix.transpose_apply, mul_comm]

/-- Entrywise conjugation is an isometry. -/
theorem norm_bar {W : Type*} [Fintype W] (v : EuclideanSpace ℂ W) :
    ‖bar v‖ = ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  exact congrArg _ (Finset.sum_congr rfl fun p _ => by simp)

/-- A `Qm`-fixed matrix vanishes when `U × V` is a single point: both index
swaps are then the identity, so the alternating sum of `mulVecE_Qm` cancels. -/
private theorem eq_zero_of_Qm_fixed_of_subsingleton [Subsingleton (U × V)]
    {K : Matrix (U × V) (U × V) ℂ} (hfix : mulVecE Qm (vec K) = vec K) : K = 0 := by
  have hswU : ∀ X : Idx U V, swU X = X := fun X => by
    have h : X.1 = X.2 := Subsingleton.elim _ _
    obtain ⟨X₁, X₂⟩ := X
    cases h
    rfl
  have hvec : vec K = 0 := by
    rw [← hfix]
    ext X
    rw [mulVecE_Qm, hswU X]
    simp
  ext p q
  simpa using congrFun (congrArg WithLp.ofLp hvec) (p, q)

/-- The fixed-point bound, applied to an orthonormal family of at most two
members.  A family of one member is padded by a unit vector orthogonal to it,
which exists unless `Fintype.card (U × V) ≤ 1`; in that case
`eq_zero_of_Qm_fixed_of_subsingleton` makes both sides vanish. -/
private theorem sum_norm_sq_le_of_orthonormal (hDS : DoubleSkewBoundQm U V)
    {K : Matrix (U × V) (U × V) ℂ} (hfix : mulVecE Qm (vec K) = vec K)
    {n : ℕ} (hn : n ≤ 2) {e : Fin n → EuclideanSpace ℂ (U × V)} (he : Orthonormal ℂ e) :
    ∑ i, ‖mulVecE K (e i)‖ ^ 2 ≤ hsNormSq K / 2 := by
  have hA0 : 0 ≤ hsNormSq K := hsNormSq_nonneg K
  interval_cases n
  · simp only [Finset.univ_eq_empty, Finset.sum_empty]
    linarith
  · rw [Fin.sum_univ_one]
    rcases le_or_gt (Fintype.card (U × V)) 1 with hcard | hcard
    · have : Subsingleton (U × V) := Fintype.card_le_one_iff_subsingleton.mp hcard
      have hK0 : K = 0 := eq_zero_of_Qm_fixed_of_subsingleton hfix
      have h1 : mulVecE K (e 0) = 0 := by
        ext p; simp [hK0]
      have h2 : hsNormSq K = 0 := by rw [hK0, hsNormSq]; simp
      rw [h1, h2]; simp
    · have he0 : e 0 ≠ 0 := fun h => by simpa [h] using he.1 0
      obtain ⟨y, hy1, hy2⟩ :
          ∃ y : EuclideanSpace ℂ (U × V), ‖y‖ = 1 ∧ inner ℂ (e 0) y = (0 : ℂ) := by
        have hne : (ℂ ∙ (e 0))ᗮ ≠ ⊥ := by
          intro hbot
          have h := Submodule.finrank_add_finrank_orthogonal (K := ℂ ∙ (e 0))
          rw [hbot, finrank_bot, finrank_span_singleton he0, finrank_euclideanSpace] at h
          omega
        obtain ⟨z, hzmem, hz0⟩ := (Submodule.ne_bot_iff _).mp hne
        have hz : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
        refine ⟨(‖z‖⁻¹ : ℂ) • z, ?_, ?_⟩
        · rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos hz, inv_mul_cancel₀ hz.ne']
        · rw [inner_smul_right,
            Submodule.mem_orthogonal_singleton_iff_inner_right.mp hzmem, mul_zero]
      have hpair := hDS K hfix (e 0) y (he.1 0) hy1 hy2
      nlinarith [sq_nonneg ‖mulVecE K y‖]
  · rw [Fin.sum_univ_two]
    exact hDS K hfix (e 0) (e 1) (he.1 0) (he.1 1) (he.2 (by decide))

/-- The projection of a low-rank matrix is small: `‖Π M‖₂² ≤ ½‖M‖₂²` whenever
`rank M ≤ 2`.  This is the converse of `doubleSkewBound_of_FGP`.

Put `K := dsProj M`, which is fixed by `Qm` since `Qm` is idempotent.  Factor
`Mᵀ = ∑ᵢ |eᵢ⟩⟨dᵢ|` with `eᵢ` orthonormal by `exists_rankFactor_rank`, so that
`M = ∑ᵢ |d̄ᵢ⟩⟨ēᵢ|` with the *right* factors orthonormal and
`∑ᵢ ‖dᵢ‖² = ‖M‖₂²`.  Self-adjointness and idempotence of the projection give
`‖K‖₂² = ⟪K, M⟫ = ∑ᵢ ⟪K eᵢ, dᵢ⟫`, so by Cauchy-Schwarz twice
`‖K‖₂² ≤ (∑ᵢ ‖K eᵢ‖²)^½ ‖M‖₂`, and the fixed-point bound applied to the
orthonormal family `eᵢ` bounds the first factor by `(½‖K‖₂²)^½`.  Cancelling one
factor of `‖K‖₂` finishes.

The family `eᵢ` has at most two members; when it has fewer, pad it to an
orthonormal pair, which is possible unless `Fintype.card (U × V) ≤ 1`, in which
case every `Qm`-fixed matrix vanishes. -/
theorem hsNormSq_dsProj_le (hDS : DoubleSkewBoundQm U V)
    (M : Matrix (U × V) (U × V) ℂ) (hrank : M.rank ≤ 2) :
    hsNormSq (dsProj M) ≤ hsNormSq M / 2 := by
  have hA0 : 0 ≤ hsNormSq (dsProj M) := hsNormSq_nonneg _
  have hB0 : 0 ≤ hsNormSq M := hsNormSq_nonneg M
  -- (a) `dsProj M` is fixed by `Qm`, since `Qm` is idempotent
  have hvK : vec (dsProj M) = mulVecE Qm (vec M) := vec_dsProj M
  have hfix : mulVecE Qm (vec (dsProj M)) = vec (dsProj M) := by
    rw [hvK, mulVecE_mul, Qm_mul_self]
  -- (b) `‖Π M‖₂² = ⟪Π M, M⟫`, by self-adjointness and idempotence
  have hb : ((hsNormSq (dsProj M) : ℝ) : ℂ) = hsInner (dsProj M) M := by
    rw [← hsInner_self, hsInner_eq_inner, hsInner_eq_inner]
    nth_rewrite 2 [hvK]
    rw [inner_mulVecE_left, Qm_conjTranspose, hfix]
  -- (c) factor `Mᵀ`, so that `M` has orthonormal *right* factors.  The index
  -- type is generalized first: `e₀`, `d₀` would otherwise have types mentioning
  -- `Mᵀ.rank`, and rewriting `M` underneath them fails the motive check.
  obtain ⟨n, hn, e, d, he, hMeq, hdM⟩ :
      ∃ n : ℕ, n ≤ 2 ∧ ∃ e d : Fin n → EuclideanSpace ℂ (U × V),
        Orthonormal ℂ e ∧ M = ∑ i, rankOne (d i) (e i) ∧
          ∑ i, ‖d i‖ ^ 2 = hsNormSq M := by
    obtain ⟨n, e₀, d₀, he₀, hMT, hn⟩ :
        ∃ (n : ℕ) (e d : Fin n → EuclideanSpace ℂ (U × V)),
          Orthonormal ℂ e ∧ Mᵀ = rankFactor e d ∧ n ≤ 2 := by
      obtain ⟨e₀, d₀, he₀, hMT⟩ := exists_rankFactor_rank Mᵀ
      exact ⟨Mᵀ.rank, e₀, d₀, he₀, hMT, rank_transpose_le hrank⟩
    refine ⟨n, hn, fun i => bar (e₀ i), fun i => bar (d₀ i),
      orthonormal_conj he₀, ?_, ?_⟩
    · have h : (Mᵀ)ᵀ = (rankFactor e₀ d₀)ᵀ := congrArg (·ᵀ) hMT
      rw [Matrix.transpose_transpose, rankFactor_eq_sum, Matrix.transpose_sum] at h
      exact h.trans (Finset.sum_congr rfl fun i _ => transpose_rankOne _ _)
    · rw [← hsNormSq_transpose M, hMT, hsNormSq_rankFactor_eq e₀ d₀ he₀]
      exact Finset.sum_congr rfl fun i _ => by rw [norm_bar]
  -- (d) each pairing is a vector pairing, so Cauchy-Schwarz applies termwise
  have hterm : ∀ i, ‖hsInner (dsProj M) (rankOne (d i) (e i))‖
      ≤ ‖d i‖ * ‖mulVecE (dsProj M) (e i)‖ := fun i => by
    rw [hsInner_rankOne_right, RCLike.norm_conj]
    exact norm_inner_le_norm _ _
  -- (e) the two Cauchy-Schwarz steps
  have hsum : hsNormSq (dsProj M) ≤ ∑ i, ‖d i‖ * ‖mulVecE (dsProj M) (e i)‖ := by
    have h0 : ((hsNormSq (dsProj M) : ℝ) : ℂ)
        = ∑ i, hsInner (dsProj M) (rankOne (d i) (e i)) := by
      rw [hb, ← hsInner_sum_right, ← hMeq]
    calc hsNormSq (dsProj M) = ‖((hsNormSq (dsProj M) : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA0]
      _ = ‖∑ i, hsInner (dsProj M) (rankOne (d i) (e i))‖ := by rw [h0]
      _ ≤ ∑ i, ‖hsInner (dsProj M) (rankOne (d i) (e i))‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖d i‖ * ‖mulVecE (dsProj M) (e i)‖ :=
          Finset.sum_le_sum fun i _ => hterm i
  have hcs : ∑ i, ‖d i‖ * ‖mulVecE (dsProj M) (e i)‖
      ≤ Real.sqrt (∑ i, ‖d i‖ ^ 2)
        * Real.sqrt (∑ i, ‖mulVecE (dsProj M) (e i)‖ ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  rw [hdM] at hcs
  -- (f) the fixed-point bound on the orthonormal family `eᵢ`
  have hS : ∑ i, ‖mulVecE (dsProj M) (e i)‖ ^ 2 ≤ hsNormSq (dsProj M) / 2 :=
    sum_norm_sq_le_of_orthonormal hDS hfix hn he
  have hSnn : (0 : ℝ) ≤ ∑ i, ‖mulVecE (dsProj M) (e i)‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  -- (g) square, then cancel one factor of `‖Π M‖₂²`
  have hAsq : hsNormSq (dsProj M) ^ 2
      ≤ hsNormSq M * ∑ i, ‖mulVecE (dsProj M) (e i)‖ ^ 2 := by
    have h2 := mul_self_le_mul_self hA0 (hsum.trans hcs)
    rw [← Real.sq_sqrt hB0, ← Real.sq_sqrt hSnn]
    nlinarith [h2]
  have hBS : hsNormSq M * (∑ i, ‖mulVecE (dsProj M) (e i)‖ ^ 2)
      ≤ hsNormSq M * (hsNormSq (dsProj M) / 2) := mul_le_mul_of_nonneg_left hS hB0
  nlinarith [hAsq, hBS, hA0, hB0]

/-- Every square matrix of rank at most two is a sum of two rank-one
operators, with a zero summand allowed. -/
theorem exists_rankOne_add_of_rank_le_two {W : Type*}
    [Fintype W] [DecidableEq W] {M : Matrix W W ℂ}
    (hrank : M.rank ≤ 2) :
    ∃ u₁ v₁ u₂ v₂ : EuclideanSpace ℂ W,
      M = rankOne u₁ v₁ + rankOne u₂ v₂ := by
  obtain ⟨e, d, _, hM⟩ := exists_rankFactor_rank M
  rw [rankFactor_eq_sum] at hM
  interval_cases h : M.rank
  · refine ⟨0, 0, 0, 0, ?_⟩
    rw [hM]
    ext p q
    simp [rankOne]
  · refine ⟨e ⟨0, by omega⟩, d ⟨0, by omega⟩, 0, 0, ?_⟩
    rw [hM]
    ext p q
    simp [rankOne]
  · refine ⟨e ⟨0, by omega⟩, d ⟨0, by omega⟩,
      e ⟨1, by omega⟩, d ⟨1, by omega⟩, ?_⟩
    rw [hM]
    ext p q
    simp [rankOne]

/-- A sum of two rank-one operators factors through a two-element index type,
hence has rank at most two. -/
theorem rank_rankOne_add_le {W : Type*} [Fintype W]
    (u₁ v₁ u₂ v₂ : EuclideanSpace ℂ W) :
    (rankOne u₁ v₁ + rankOne u₂ v₂).rank ≤ 2 := by
  have hfac : rankOne u₁ v₁ + rankOne u₂ v₂
      = (Matrix.of fun (p : W) (i : Fin 2) => ![u₁ p, u₂ p] i)
        * (Matrix.of fun (i : Fin 2) (q : W) => ![conj (v₁ q), conj (v₂ q)] i) := by
    ext p q
    simp [Matrix.mul_apply, rankOne, Fin.sum_univ_two]
  rw [hfac]
  exact (Matrix.rank_mul_le_left _ _).trans (by
    simpa using Matrix.rank_le_card_width
      (Matrix.of fun (p : W) (i : Fin 2) => ![u₁ p, u₂ p] i))

/-- The explicit `k`-term formulation of the Choi bound is exactly the direct
pure-Schmidt-rank formulation. -/
theorem choiKBound_iff_pureSchmidtKBound
    {W : Type*} [Fintype W] [DecidableEq W]
    {J : Matrix (W × W) (W × W) ℂ} {k : ℕ} {β : ℝ} :
    ChoiKBound J k β ↔ PureSchmidtKBound J k β := by
  constructor
  · intro h z hz
    have hrank : (unvec z).rank ≤ k := by
      simpa [pureSchmidtRank] using hz
    obtain ⟨u, v, hdecomp⟩ :=
      (rank_le_iff_exists_sum_rankOne (unvec z)).mp hrank
    have hb := h u v
    rw [← hdecomp] at hb
    simpa [hsNormSq_eq_norm_sq] using hb
  · intro h u v
    let M : Matrix W W ℂ := ∑ i, rankOne (u i) (v i)
    have hrank : pureSchmidtRank (vec M) ≤ k := by
      rw [pureSchmidtRank_vec]
      exact (rank_le_iff_exists_sum_rankOne M).mpr ⟨u, v, rfl⟩
    have hb := h (vec M) hrank
    simpa [M, hsNormSq_eq_norm_sq] using hb

/-- The rank-two Choi bound used by pair amplification is literally the bound
over vectors of pure Schmidt rank at most two. -/
theorem choiTwoBound_iff_pureSchmidtKBound_two
    {W : Type*} [Fintype W] [DecidableEq W]
    {J : Matrix (W × W) (W × W) ℂ} {β : ℝ} :
    ChoiTwoBound J β ↔ PureSchmidtKBound J 2 β :=
  choiTwoBound_iff_choiKBound_two.trans
    choiKBound_iff_pureSchmidtKBound

/-- Fu--Gao--Park's four-vector formulation is exactly its usual
Schmidt-rank-two formulation. -/
theorem fgpBound_iff_pureSchmidtKBound_two :
    FGPBound U V ↔
      PureSchmidtKBound
        (Qm : Matrix (Idx U V) (Idx U V) ℂ) 2 (1 / 4) :=
  choiTwoBound_Qm_iff.symm.trans
    choiTwoBound_iff_pureSchmidtKBound_two

/-- **Fu-Gao-Park's estimate, from the double-skew bound.**  The converse of
`doubleSkewBound_of_FGP`, so the two are equivalent. -/
theorem FGPBound_of_doubleSkewBoundQm (hDS : DoubleSkewBoundQm U V) : FGPBound U V := by
  intro u₁ v₁ u₂ v₂
  rw [← norm_mulVecE_Qm_sq, ← vec_dsProj, ← hsNormSq_eq_norm_sq]
  exact hsNormSq_dsProj_le hDS _ (rank_rankOne_add_le u₁ v₁ u₂ v₂)

/-- **Fu-Gao-Park's Theorem 2.4, unconditionally.**

Together with `doubleSkewBound_of_FGP` this closes the loop: the estimate
Fu-Gao-Park state and the double-skew action bound of the manuscript are
equivalent, and both are proved from the Autonne-Takagi factorization.

The homogeneous four-vector form `FGPBound` is identified with the direct
pure-Schmidt-rank-two statement by
`fgpBound_iff_pureSchmidtKBound_two`. -/
theorem fgpBound_holds : FGPBound U V :=
  FGPBound_of_doubleSkewBoundQm doubleSkewBoundQm_holds

end RankR
