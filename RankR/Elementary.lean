/-
The routine layer: rank monotonicity, the range-factorization identities of
`lem:partial-trace-contractions`, and the finite-sum reindexings they need.
-/
import RankR.HS
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Positivity.Finset

namespace RankR

open Matrix Finset ComplexConjugate

/-- The gap of `eq:rank-monotonicity` in factored form.  Both the non-strict and
the strict reading of that display come from this one identity: the first factor
is the increment in the rank parameter, the second is what the trace-rank bound
controls. -/
theorem rank_gap {a t : ℝ} {r₀ r : ℕ} (hr₀ : (r₀ : ℝ) ≠ 0) (hr : (r : ℝ) ≠ 0) :
    (r : ℝ) * a + (1 / r) * t - ((r₀ : ℝ) * a + (1 / r₀) * t)
      = ((r : ℝ) - r₀) * (a - t / ((r : ℝ) * r₀)) := by
  field_simp; ring

/-- `eq:rank-monotonicity`: the passage from the exact rank `r₀` to any `r ≥ r₀`.

Stated abstractly in `a = ‖C‖₂²` and the nonnegative `t = |Tr C|²`, with `htr`
the trace-rank bound `|Tr C|² ≤ r₀‖C‖₂²`.  The manuscript's chain is
  (r-r₀)a - (r-r₀)/(r r₀) t  ≥  (r-r₀)a - (r-r₀)/r a  ≥  0.

Nonnegativity of `a` is not assumed: it follows from `ht` and `htr`. -/
theorem rank_mono {a t : ℝ} (ht : 0 ≤ t) {r₀ r : ℕ}
    (hr₀ : 0 < r₀) (hle : r₀ ≤ r) (htr : t ≤ r₀ * a) :
    (r₀ : ℝ) * a + (1 / r₀) * t ≤ (r : ℝ) * a + (1 / r) * t := by
  have h1 : (1 : ℝ) ≤ (r₀ : ℝ) := by exact_mod_cast hr₀
  have h2 : (r₀ : ℝ) ≤ (r : ℝ) := by exact_mod_cast hle
  have hr0 : (0 : ℝ) < (r₀ : ℝ) := by linarith
  have hrr : (0 : ℝ) < (r : ℝ) := by linarith
  rw [← sub_nonneg, rank_gap hr0.ne' hrr.ne']
  apply mul_nonneg (by linarith)
  rw [sub_nonneg, div_le_iff₀ (by positivity)]
  nlinarith

/-- The strict form of `eq:rank-monotonicity`, used for the sharpness assertion
of `thm:rank_r`: for `a > 0` the passage to a strictly larger `r` is strict.

The same chain, but `r₀ < r` forces `r ≥ 2`, so the second step now loses
`(r-r₀)(1-1/r)a > 0`.  Unlike `rank_mono` this needs no sign condition on `t` at
all: `t ≤ r₀a` and `r ≥ 2` already put `t/(r r₀)` strictly below `a`. -/
theorem rank_mono_strict {a t : ℝ} (ha : 0 < a) {r₀ r : ℕ}
    (hr₀ : 0 < r₀) (hlt : r₀ < r) (htr : t ≤ r₀ * a) :
    (r₀ : ℝ) * a + (1 / r₀) * t < (r : ℝ) * a + (1 / r) * t := by
  have h1 : (1 : ℝ) ≤ (r₀ : ℝ) := by exact_mod_cast hr₀
  have h2 : (r₀ : ℝ) + 1 ≤ (r : ℝ) := by exact_mod_cast hlt
  have hr0 : (0 : ℝ) < (r₀ : ℝ) := by linarith
  have hrr : (0 : ℝ) < (r : ℝ) := by linarith
  rw [← sub_pos, rank_gap hr0.ne' hrr.ne']
  apply mul_pos (by linarith)
  rw [sub_pos, div_lt_iff₀ (by positivity)]
  nlinarith [mul_pos hr0 ha]

/-! ## The range factorization, entry by entry

The factorization and the vectors it is built from are defined coordinatewise,
and summing over the `s` columns needs nothing of `W`; only the norms and
pairings below sum over `W` itself. -/

section Entrywise

variable {W : Type*} {s : ℕ}

/-- The range factorization `C = ∑ᵢ |eᵢ⟩⟨dᵢ|` of `lem:partial-trace-contractions`.
Zero columns `dᵢ = 0` are allowed, as in Prop 4.1. -/
def rankFactor (e d : Fin s → EuclideanSpace ℂ W) : Matrix W W ℂ :=
  Matrix.of fun p q => ∑ i, e i p * conj (d i q)

@[simp] theorem rankFactor_apply (e d : Fin s → EuclideanSpace ℂ W) (p q : W) :
    rankFactor e d p q = ∑ i, e i p * conj (d i q) := rfl

/-- `δ = ∑ᵢ dᵢ ⊗ qᵢ ∈ (U ⊗ V) ⊗ Q`, the unnormalized vector of section 3. -/
def delta (d : Fin s → EuclideanSpace ℂ W) : EuclideanSpace ℂ (W × Fin s) :=
  WithLp.toLp 2 (fun pi => d pi.2 pi.1)

@[simp] theorem delta_apply (d : Fin s → EuclideanSpace ℂ W) (pi : W × Fin s) :
    delta d pi = d pi.2 pi.1 := rfl

/-- The rank-one operator `|x⟩⟨y|`, with the section 1 convention
`vec (|x⟩⟨y|) = x ⊗ conj y`. -/
def rankOne (x y : EuclideanSpace ℂ W) : Matrix W W ℂ :=
  Matrix.of fun p q => x p * conj (y q)

theorem rankFactor_eq_sum (e d : Fin s → EuclideanSpace ℂ W) :
    rankFactor e d = ∑ i, rankOne (e i) (d i) := by
  ext p q
  simp [rankFactor, rankOne, Matrix.sum_apply]

end Entrywise

section SchmidtDecomposition

variable {W : Type*} [Fintype W] [DecidableEq W] {k : ℕ}

/-- A square coefficient matrix has rank at most `k` exactly when it is a sum
of `k` rank-one matrices.  Zero summands provide the padding when the rank is
strictly smaller than `k`. -/
theorem rank_le_iff_exists_sum_rankOne (M : Matrix W W ℂ) :
    M.rank ≤ k ↔
      ∃ u v : Fin k → EuclideanSpace ℂ W,
        M = ∑ i, rankOne (u i) (v i) := by
  constructor
  · intro hrank
    have hcard : M.rank ≤ Fintype.card (Fin k) := by simpa using hrank
    obtain ⟨X, Y, hXY⟩ :=
      (rank_le_card_iff_exists_mul (A := Fin k) M).mp hcard
    let u : Fin k → EuclideanSpace ℂ W :=
      fun i => WithLp.toLp 2 fun p => X p i
    let v : Fin k → EuclideanSpace ℂ W :=
      fun i => WithLp.toLp 2 fun q => conj (Y i q)
    refine ⟨u, v, ?_⟩
    rw [← hXY]
    ext p q
    simp [Matrix.mul_apply, Matrix.sum_apply, rankOne, u, v]
  · rintro ⟨u, v, rfl⟩
    have hfac :
        ∃ X : Matrix W (Fin k) ℂ, ∃ Y : Matrix (Fin k) W ℂ,
          X * Y = ∑ i, rankOne (u i) (v i) := by
      refine ⟨Matrix.of fun p i => u i p,
        Matrix.of fun i q => conj (v i q), ?_⟩
      ext p q
      simp [Matrix.mul_apply, Matrix.sum_apply, rankOne]
    have hcard :=
      (rank_le_card_iff_exists_mul
        (A := Fin k) (∑ i, rankOne (u i) (v i))).mpr hfac
    simpa using hcard

end SchmidtDecomposition

section Contractions

variable {W : Type*} [Fintype W] {s : ℕ}

theorem norm_delta (d : Fin s → EuclideanSpace ℂ W) :
    ‖delta d‖ ^ 2 = ∑ i, ‖d i‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fintype.sum_prod_type,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  rfl

/-- The one genuine computation: `⟪|x⟩⟨y|, |z⟩⟨w|⟫ = ⟪x,z⟫ · conj ⟪y,w⟫`. -/
theorem hsInner_rankOne (x y z w : EuclideanSpace ℂ W) :
    hsInner (rankOne x y) (rankOne z w) = inner ℂ x z * conj (inner ℂ y w) := by
  simp only [hsInner, rankOne, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, RCLike.star_def, Matrix.of_apply, map_mul,
    Complex.conj_conj, PiLp.inner_apply, RCLike.inner_apply', map_sum]
  rw [Finset.sum_mul_sum, Finset.sum_comm]
  exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => by ring

/-- The Gram expansion underlying `eq:contraction-norm`:
`‖∑ᵢ |eᵢ⟩⟨dᵢ|‖₂² = ∑ᵢⱼ ⟪eᵢ,eⱼ⟫ · conj ⟪dᵢ,dⱼ⟫`.  No orthonormality yet. -/
theorem hsNormSq_rankFactor (e d : Fin s → EuclideanSpace ℂ W) :
    ((hsNormSq (rankFactor e d) : ℝ) : ℂ)
      = ∑ i, ∑ j, inner ℂ (e i) (e j) * conj (inner ℂ (d i) (d j)) := by
  rw [← hsInner_self, rankFactor_eq_sum, hsInner_sum_sum]
  exact Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => hsInner_rankOne _ _ _ _

/-- `eq:contraction-norm`: `⟪δ, δ⟫ = ‖C‖₂²`.
The one identity that uses orthonormality of the `eᵢ`. -/
theorem contraction_norm (e d : Fin s → EuclideanSpace ℂ W)
    (he : Orthonormal ℂ e) :
    hsNormSq (rankFactor e d) = ‖delta d‖ ^ 2 := by
  rw [norm_delta, ← Complex.ofReal_inj, hsNormSq_rankFactor]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · have h1 : inner ℂ (e i) (e i) = 1 := by
      rw [inner_self_eq_norm_sq_to_K, he.1 i]; norm_num
    rw [h1, one_mul, inner_self_eq_norm_sq_to_K]
    simp
  · intro j _ hj
    rw [he.2 (Ne.symm hj), zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- `eq:contraction-trace`: the trace of the range factorization. -/
theorem contraction_trace (e d : Fin s → EuclideanSpace ℂ W) :
    (rankFactor e d).trace = ∑ i, inner ℂ (d i) (e i) := by
  simp only [Matrix.trace, Matrix.diag_apply, rankFactor_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [PiLp.inner_apply]
  simp

/-- With orthonormal `eᵢ`, `‖C‖₂² = ∑ᵢ ‖dᵢ‖²`. -/
theorem hsNormSq_rankFactor_eq (e d : Fin s → EuclideanSpace ℂ W)
    (he : Orthonormal ℂ e) :
    hsNormSq (rankFactor e d) = ∑ i, ‖d i‖ ^ 2 := by
  rw [contraction_norm e d he, norm_delta]

/-- The trace-rank Cauchy-Schwarz `|Tr C|² ≤ s ‖C‖₂²` (section 3, used to feed
`rank_mono`).  The manuscript proves it via the range projection `P`; with the
range factorization already in hand it is the discrete Cauchy-Schwarz. -/
theorem normSq_trace_le (e d : Fin s → EuclideanSpace ℂ W) (he : Orthonormal ℂ e) :
    Complex.normSq (rankFactor e d).trace ≤ s * hsNormSq (rankFactor e d) := by
  rw [contraction_trace, Complex.normSq_eq_norm_sq, hsNormSq_rankFactor_eq e d he]
  have h1 : ‖∑ i, inner ℂ (d i) (e i)‖ ≤ ∑ i, ‖d i‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    have h := norm_inner_le_norm (𝕜 := ℂ) (d i) (e i)
    rwa [he.1 i, mul_one] at h
  have h2 : (∑ i, ‖d i‖) ^ 2 ≤ (s : ℝ) * ∑ i, ‖d i‖ ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin s)))
      (f := fun i => ‖d i‖)
    simpa using h
  have h0 : (0 : ℝ) ≤ ‖∑ i, inner ℂ (d i) (e i)‖ := norm_nonneg _
  have h3 : (0 : ℝ) ≤ ∑ i, ‖d i‖ :=
    Finset.sum_nonneg fun i _ => norm_nonneg (d i)
  nlinarith

end Contractions

/-- Swap the outer and inner index pairs of a four-fold sum.  Used to match the
two expansions of `eq:contraction-U`. -/
theorem sum4_swap {A B C D M : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [AddCommMonoid M] (F : A → B → C → D → M) :
    ∑ c, ∑ d, ∑ a, ∑ b, F a b c d = ∑ a, ∑ b, ∑ c, ∑ d, F a b c d := by
  have h1 : ∑ c, ∑ d, ∑ a, ∑ b, F a b c d
      = ∑ cd : C × D, ∑ ab : A × B, F ab.1 ab.2 cd.1 cd.2 := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ =>
      (Fintype.sum_prod_type (fun ab : A × B => F ab.1 ab.2 c d)).symm
  have h2 : ∑ a, ∑ b, ∑ c, ∑ d, F a b c d
      = ∑ ab : A × B, ∑ cd : C × D, F ab.1 ab.2 cd.1 cd.2 := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      (Fintype.sum_prod_type (fun cd : C × D => F a b cd.1 cd.2)).symm
  rw [h1, h2, Finset.sum_comm]

/-- Reindex a six-fold sum `(a,b,i,a',i',c) ↦ (i,i',a,a',c,b)`, via an explicit
`Equiv` on the product type. -/
theorem sum6_perm {A B I C M : Type*} [Fintype A] [Fintype B] [Fintype I] [Fintype C]
    [AddCommMonoid M] (F : A → B → I → A → I → C → M) :
    (∑ a, ∑ b, ∑ i, ∑ a', ∑ i', ∑ c, F a b i a' i' c)
      = ∑ i, ∑ i', ∑ a, ∑ a', ∑ c, ∑ b, F a b i a' i' c := by
  have hL : (∑ a, ∑ b, ∑ i, ∑ a', ∑ i', ∑ c, F a b i a' i' c)
      = ∑ p : A × B × I × A × I × C,
          F p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 := by
    simp only [Fintype.sum_prod_type]
  have hR : (∑ i, ∑ i', ∑ a, ∑ a', ∑ c, ∑ b, F a b i a' i' c)
      = ∑ q : I × I × A × A × C × B,
          F q.2.2.1 q.2.2.2.2.2 q.1 q.2.2.2.1 q.2.1 q.2.2.2.2.1 := by
    simp only [Fintype.sum_prod_type]
  rw [hL, hR]
  exact Fintype.sum_equiv
    { toFun := fun p : A × B × I × A × I × C =>
        (p.2.2.1, p.2.2.2.2.1, p.1, p.2.2.2.1, p.2.2.2.2.2, p.2.1)
      invFun := fun q : I × I × A × A × C × B =>
        (q.2.2.1, q.2.2.2.2.2, q.1, q.2.2.2.1, q.2.1, q.2.2.2.2.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl } _ _ (fun _ => rfl)

/-- The mirrored six-fold reindexing `(a,b,i,b',i',c) ↦ (i,i',b,b',c,a)`, for the
`V`-marginal.  A separate helper because the collapsed index sits in a different
slot than in `sum6_perm`. -/
theorem sum6_perm' {A B I C M : Type*} [Fintype A] [Fintype B] [Fintype I] [Fintype C]
    [AddCommMonoid M] (F : A → B → I → B → I → C → M) :
    (∑ a, ∑ b, ∑ i, ∑ b', ∑ i', ∑ c, F a b i b' i' c)
      = ∑ i, ∑ i', ∑ b, ∑ b', ∑ c, ∑ a, F a b i b' i' c := by
  have hL : (∑ a, ∑ b, ∑ i, ∑ b', ∑ i', ∑ c, F a b i b' i' c)
      = ∑ p : A × B × I × B × I × C,
          F p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 := by
    simp only [Fintype.sum_prod_type]
  have hR : (∑ i, ∑ i', ∑ b, ∑ b', ∑ c, ∑ a, F a b i b' i' c)
      = ∑ q : I × I × B × B × C × A,
          F q.2.2.2.2.2 q.2.2.1 q.1 q.2.2.2.1 q.2.1 q.2.2.2.2.1 := by
    simp only [Fintype.sum_prod_type]
  rw [hL, hR]
  exact Fintype.sum_equiv
    { toFun := fun p : A × B × I × B × I × C =>
        (p.2.2.1, p.2.2.2.2.1, p.2.1, p.2.2.2.1, p.2.2.2.2.2, p.1)
      invFun := fun q : I × I × B × B × C × A =>
        (q.2.2.2.2.2, q.2.2.1, q.1, q.2.2.2.1, q.2.1, q.2.2.2.2.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl } _ _ (fun _ => rfl)

/-! ## The two marginals

`Tr_U` sums over `U` and leaves `V` untouched, so its lemmas need `Fintype U`
and not `Fintype V`; `Tr_V` is the mirror.  Each `omit` below records which of
the two factors the declaration under it actually contracts. -/

section Product

variable {U V : Type*} [Fintype U] [Fintype V] {s : ℕ}

omit [Fintype V] in
@[simp] theorem ptraceU_apply (C : Matrix (U × V) (U × V) ℂ) (b c : V) :
    ptraceU C b c = ∑ a, C (a, b) (a, c) := rfl

omit [Fintype U] in
@[simp] theorem ptraceV_apply (C : Matrix (U × V) (U × V) ℂ) (a a' : U) :
    ptraceV C a a' = ∑ b, C (a, b) (a', b) := rfl

omit [Fintype V] in
theorem ptraceU_sum (A : Fin s → Matrix (U × V) (U × V) ℂ) :
    ptraceU (∑ i, A i) = ∑ i, ptraceU (A i) := by
  ext b c
  simp only [ptraceU_apply, Matrix.sum_apply]
  exact Finset.sum_comm

omit [Fintype U] in
theorem ptraceV_sum (A : Fin s → Matrix (U × V) (U × V) ℂ) :
    ptraceV (∑ i, A i) = ∑ i, ptraceV (A i) := by
  ext a a'
  simp only [ptraceV_apply, Matrix.sum_apply]
  exact Finset.sum_comm

/-- `Tr_U` of a rank-one operator, paired with another: the `U`-marginal Gram
expansion.  This is the computational core of `eq:contraction-U`. -/
theorem hsInner_ptraceU_rankOne (x y z w : EuclideanSpace ℂ (U × V)) :
    hsInner (ptraceU (rankOne x y)) (ptraceU (rankOne z w))
      = ∑ a, ∑ a', (∑ b, conj (x (a, b)) * z (a', b)) *
                   (∑ c, y (a, c) * conj (w (a', c))) := by
  have hL : hsInner (ptraceU (rankOne x y)) (ptraceU (rankOne z w))
      = ∑ c, ∑ b, ∑ a, ∑ a',
          conj (x (a, b)) * z (a', b) * (y (a, c) * conj (w (a', c))) := by
    simp only [hsInner, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, RCLike.star_def, rankOne,
      Matrix.of_apply, map_sum, map_mul, Complex.conj_conj]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => by ring
  have hR : (∑ a, ∑ a', (∑ b, conj (x (a, b)) * z (a', b)) *
                        (∑ c, y (a, c) * conj (w (a', c))))
      = ∑ a, ∑ a', ∑ b, ∑ c,
          conj (x (a, b)) * z (a', b) * (y (a, c) * conj (w (a', c))) := by
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ =>
      Finset.sum_mul_sum _ _ _ _
  rw [hL, hR, sum4_swap]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => Finset.sum_comm

/-- The `V`-marginal counterpart, the core of `eq:contraction-V`. -/
theorem hsInner_ptraceV_rankOne (x y z w : EuclideanSpace ℂ (U × V)) :
    hsInner (ptraceV (rankOne x y)) (ptraceV (rankOne z w))
      = ∑ b, ∑ b', (∑ a, conj (x (a, b)) * z (a, b')) *
                   (∑ a', y (a', b) * conj (w (a', b'))) := by
  have hL : hsInner (ptraceV (rankOne x y)) (ptraceV (rankOne z w))
      = ∑ a', ∑ a, ∑ b, ∑ b',
          conj (x (a, b)) * z (a, b') * (y (a', b) * conj (w (a', b'))) := by
    simp only [hsInner, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, RCLike.star_def, rankOne,
      Matrix.of_apply, map_sum, map_mul, Complex.conj_conj]
    refine Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => by ring
  have hR : (∑ b, ∑ b', (∑ a, conj (x (a, b)) * z (a, b')) *
                        (∑ a', y (a', b) * conj (w (a', b'))))
      = ∑ b, ∑ b', ∑ a, ∑ a',
          conj (x (a, b)) * z (a, b') * (y (a', b) * conj (w (a', b'))) := by
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ =>
      Finset.sum_mul_sum _ _ _ _
  rw [hL, hR, sum4_swap]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => Finset.sum_comm

/-- **`eq:contraction-U`** in Gram form: the `U`-marginal expansion of
`‖Tr_U C‖₂²` for a range factorization `C = ∑ᵢ |eᵢ⟩⟨dᵢ|`.

The manuscript writes this (proof of `lem:partial-trace-contractions`) as
`‖Tr_U C‖₂² = ∑_{i,j} ∑_{a,a'} ∑_{b,c} e_{i,ab} conj d_{i,ac} conj e_{j,a'b} d_{j,a'c}`;
the form below is that sum with the `(i,j)` roles conjugated, which is the same
real number since the total is self-conjugate under `i ↔ j`. -/
theorem hsNormSq_ptraceU_rankFactor (e d : Fin s → EuclideanSpace ℂ (U × V)) :
    ((hsNormSq (ptraceU (rankFactor e d)) : ℝ) : ℂ)
      = ∑ i, ∑ j, ∑ a, ∑ a',
          (∑ b, conj (e i (a, b)) * e j (a', b)) *
          (∑ c, d i (a, c) * conj (d j (a', c))) := by
  rw [← hsInner_self, rankFactor_eq_sum, ptraceU_sum, hsInner_sum_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    hsInner_ptraceU_rankOne _ _ _ _

/-- **`eq:contraction-V`** in Gram form. -/
theorem hsNormSq_ptraceV_rankFactor (e d : Fin s → EuclideanSpace ℂ (U × V)) :
    ((hsNormSq (ptraceV (rankFactor e d)) : ℝ) : ℂ)
      = ∑ i, ∑ j, ∑ b, ∑ b',
          (∑ a, conj (e i (a, b)) * e j (a, b')) *
          (∑ a', d i (a', b) * conj (d j (a', b'))) := by
  rw [← hsInner_self, rankFactor_eq_sum, ptraceV_sum, hsInner_sum_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    hsInner_ptraceV_rankOne _ _ _ _

end Product

end RankR
