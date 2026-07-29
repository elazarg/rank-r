/-
Algebraic cores of the applications in Section 4 of the manuscript.

The paper phrases the score results as infima over nonzero rank-constrained
matrices.  Here they are recorded in the equivalent audit-friendly form:

* a pointwise lower bound for every admissible matrix; and
* an explicit rank-exact matrix attaining the bound.

This avoids adding an extended-real `sInf` layer while checking every
inequality and every claimed extremizer used to identify the infimum.
-/
import RankR.OneSided
import RankR.Optimal
import RankR.Results
import RankR.BlockPos

namespace RankR

open Matrix Finset

section Scores

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]

/-- `q^{(2)}(-t,C)` from `eq:q2`. -/
def twoCopyScore (t : ℝ) (C : Matrix (U × V) (U × V) ℂ) : ℝ :=
  hsNormSq C
    - t * (hsNormSq (ptraceU C) + hsNormSq (ptraceV C))
    + t ^ 2 * Complex.normSq C.trace

/-- `q_{a,b}(C)` from `eq:q2-asymmetric`, with `a` on `Tr_U`. -/
def asymmetricScore (a b : ℝ) (C : Matrix (U × V) (U × V) ℂ) : ℝ :=
  hsNormSq C
    - a * hsNormSq (ptraceU C)
    - b * hsNormSq (ptraceV C)
    + a * b * Complex.normSq C.trace

/-- Exchange the two local tensor factors of a square bipartite matrix. -/
def swapFactors (C : Matrix (V × U) (V × U) ℂ) : Matrix (U × V) (U × V) ℂ :=
  Matrix.reindex (Equiv.prodComm V U) (Equiv.prodComm V U) C

@[simp]
theorem swapFactors_apply (C : Matrix (V × U) (V × U) ℂ)
    (p q : U × V) : swapFactors C p q = C (p.2, p.1) (q.2, q.1) := rfl

@[simp]
theorem rank_swapFactors (C : Matrix (V × U) (V × U) ℂ) :
    (swapFactors C).rank = C.rank :=
  Matrix.rank_reindex (Equiv.prodComm V U) (Equiv.prodComm V U) C

@[simp]
theorem hsNormSq_swapFactors (C : Matrix (V × U) (V × U) ℂ) :
    hsNormSq (swapFactors C) = hsNormSq C := by
  simp only [hsNormSq, Fintype.sum_prod_type, swapFactors_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_comm

@[simp]
theorem trace_swapFactors (C : Matrix (V × U) (V × U) ℂ) :
    (swapFactors C).trace = C.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_prod_type, swapFactors_apply]
  rw [Finset.sum_comm]

@[simp]
theorem ptraceU_swapFactors (C : Matrix (V × U) (V × U) ℂ) :
    ptraceU (swapFactors C) = ptraceV C := by
  ext v v'
  rfl

@[simp]
theorem ptraceV_swapFactors (C : Matrix (V × U) (V × U) ℂ) :
    ptraceV (swapFactors C) = ptraceU C := by
  ext u u'
  rfl

@[simp]
theorem asymmetricScore_swapFactors (a b : ℝ)
    (C : Matrix (V × U) (V × U) ℂ) :
    asymmetricScore a b (swapFactors C) = asymmetricScore b a C := by
  simp only [asymmetricScore, hsNormSq_swapFactors, ptraceU_swapFactors,
    ptraceV_swapFactors, trace_swapFactors]
  ring

/-- The first branch of `prop:exact-q2-score`, as a pointwise bound. -/
theorem twoCopyScore_lower_of_le_inv {r : ℕ} (hr : 0 < r)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / (r : ℝ))
    (C : Matrix (U × V) (U × V) ℂ) (hrank : C.rank ≤ r) :
    (1 - t) * (1 - r * t) * hsNormSq C ≤ twoCopyScore t C := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hmain := rank_r_partial_trace C r hrank
  have hmain_t := mul_le_mul_of_nonneg_left hmain ht0
  have htrace : Complex.normSq C.trace ≤ (r : ℝ) * hsNormSq C := by
    exact (normSq_trace_le_rank C).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hrank) (hsNormSq_nonneg C))
  have hcoef : t ^ 2 - t * (1 / (r : ℝ)) ≤ 0 := by
    have hinv : 0 ≤ 1 / (r : ℝ) := (one_div_nonneg.mpr hrR.le)
    nlinarith
  have hcoef_use := mul_le_mul_of_nonpos_left htrace hcoef
  have hri : (r : ℝ) * (1 / (r : ℝ)) = 1 := by field_simp
  calc
    (1 - t) * (1 - r * t) * hsNormSq C
        = (1 - r * t) * hsNormSq C
          + (t ^ 2 - t * (1 / (r : ℝ))) * ((r : ℝ) * hsNormSq C) := by
            field_simp [ne_of_gt hrR] <;> ring
    _ ≤ (1 - r * t) * hsNormSq C
          + (t ^ 2 - t * (1 / (r : ℝ))) * Complex.normSq C.trace := by
            linarith
    _ = hsNormSq C
          - t * ((r : ℝ) * hsNormSq C
            + (1 / (r : ℝ)) * Complex.normSq C.trace)
          + t ^ 2 * Complex.normSq C.trace := by ring
    _ ≤ twoCopyScore t C := by
      unfold twoCopyScore
      linarith

/-- The second branch of `prop:exact-q2-score`, as a pointwise bound. -/
theorem twoCopyScore_lower_of_inv_le {r : ℕ} (hr : 0 < r)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : 1 / (r : ℝ) ≤ t)
    (C : Matrix (U × V) (U × V) ℂ) (hrank : C.rank ≤ r) :
    (1 - r * t) * hsNormSq C ≤ twoCopyScore t C := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hmain := rank_r_partial_trace C r hrank
  have hmain_t := mul_le_mul_of_nonneg_left hmain ht0
  have hcoef : 0 ≤ t ^ 2 - t * (1 / (r : ℝ)) := by
    nlinarith [one_div_nonneg.mpr hrR.le]
  have htrace0 := Complex.normSq_nonneg C.trace
  calc
    (1 - r * t) * hsNormSq C
        ≤ (1 - r * t) * hsNormSq C
          + (t ^ 2 - t * (1 / (r : ℝ))) * Complex.normSq C.trace := by
            exact le_add_of_nonneg_right (mul_nonneg hcoef htrace0)
    _ = hsNormSq C
          - t * ((r : ℝ) * hsNormSq C
            + (1 / (r : ℝ)) * Complex.normSq C.trace)
          + t ^ 2 * Complex.normSq C.trace := by ring
    _ ≤ twoCopyScore t C := by
      unfold twoCopyScore
      linarith

/-- The traceful extremizer attains the first score branch. -/
theorem twoCopyScore_projWit_same {S : Finset U} {x : V} {r : ℕ}
    (hS : S.card = r) (t : ℝ) :
    twoCopyScore t (projWit S x x)
      = (1 - t) * (1 - r * t) * hsNormSq (projWit S x x) := by
  rw [twoCopyScore, hsNormSq_projWit, hsNormSq_ptraceU_projWit,
    hsNormSq_ptraceV_projWit, trace_projWit, if_pos rfl, if_pos rfl, hS,
    Complex.normSq_natCast]
  push_cast
  ring

/-- The traceless extremizer attains the second score branch. -/
theorem twoCopyScore_projWit_orthogonal {S : Finset U} {x₀ x₁ : V} (hx : x₀ ≠ x₁)
    {r : ℕ} (hS : S.card = r) (t : ℝ) :
    twoCopyScore t (projWit S x₀ x₁)
      = (1 - r * t) * hsNormSq (projWit S x₀ x₁) := by
  rw [twoCopyScore, hsNormSq_projWit, hsNormSq_ptraceU_projWit,
    hsNormSq_ptraceV_projWit, trace_projWit, if_neg hx, if_neg hx, hS]
  simp
  push_cast
  ring

/-- The unrolled block-positivity condition for the symmetric two-copy score. -/
def TwoCopyNonnegative (r : ℕ) (t : ℝ) : Prop :=
  ∀ C : Matrix (U × V) (U × V) ℂ, C.rank ≤ r → 0 ≤ twoCopyScore t C

/-- `cor:two-copy-block-positive` in the nontrivial range `r ≤ dim U`,
expressed directly as the score condition.  The opposite orientation follows by
interchanging the two factors. -/
theorem twoCopyNonnegative_iff {r : ℕ} (hr : 0 < r)
    (hU : r ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    {t : ℝ} (ht0 : 0 ≤ t) :
    TwoCopyNonnegative (U := U) (V := V) r t ↔ t ≤ 1 / (r : ℝ) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  constructor
  · intro h
    obtain ⟨S, -, hcard⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset U)) (by simpa using hU)
    obtain ⟨x₀, x₁, hx⟩ :=
      Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card V)
    have hrank : (projWit S x₀ x₁).rank ≤ r := by
      rw [rank_projWit, hcard]
    have hkey := h (projWit S x₀ x₁) hrank
    rw [twoCopyScore_projWit_orthogonal hx hcard, hsNormSq_projWit, hcard] at hkey
    have hone : 0 ≤ 1 - (r : ℝ) * t := by
      exact nonneg_of_mul_nonneg_left hkey hrR
    rw [le_div_iff₀ hrR]
    nlinarith
  · intro ht C hrank
    have hinv_le_one : 1 / (r : ℝ) ≤ 1 := by
      rw [div_le_one hrR]
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hr))
    have hrt : (r : ℝ) * t ≤ 1 := by
      have hmul := mul_le_mul_of_nonneg_left ht hrR.le
      have hri : (r : ℝ) * (1 / (r : ℝ)) = 1 := by field_simp
      rwa [hri] at hmul
    have hlower := twoCopyScore_lower_of_le_inv hr ht0 ht C hrank
    exact hlower.trans' <|
      mul_nonneg
        (mul_nonneg (sub_nonneg.mpr (ht.trans hinv_le_one)) (sub_nonneg.mpr hrt))
        (hsNormSq_nonneg C)

/-- The endpoint witness in `cor:adjacent-rank-gap`, before vector normalization. -/
theorem twoCopyScore_adjacent_endpoint {S : Finset U} {x₀ x₁ : V} (hx : x₀ ≠ x₁)
    {r : ℕ} (hr : 0 < r) (hS : S.card = r + 1) :
    twoCopyScore (1 / (r : ℝ)) (projWit S x₀ x₁)
      = -(1 / (r : ℝ)) * hsNormSq (projWit S x₀ x₁) := by
  rw [twoCopyScore_projWit_orthogonal hx hS]
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  push_cast
  field_simp [ne_of_gt hrR]
  ring

/-- The uniform positive-margin half of `rem:strict-rank-gap`. -/
theorem twoCopyScore_strict_separation_lower {r : ℕ} (hr : 0 < r)
    {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / ((r + 1 : ℕ) : ℝ))
    (C : Matrix (U × V) (U × V) ℂ) (hrank : C.rank ≤ r) :
    ε * (1 - (1 - ε) / (r : ℝ)) * hsNormSq C
      ≤ twoCopyScore ((1 - ε) / (r : ℝ)) C := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hr1R : (0 : ℝ) < (r + 1 : ℕ) := by positivity
  have hinv_le_one : 1 / ((r + 1 : ℕ) : ℝ) ≤ 1 := by
    rw [div_le_one hr1R]
    norm_num
  have hε1 : ε < 1 := hε.trans_le hinv_le_one
  have ht0 : 0 ≤ (1 - ε) / (r : ℝ) :=
    div_nonneg (by linarith) hrR.le
  have ht : (1 - ε) / (r : ℝ) ≤ 1 / (r : ℝ) := by
    exact (div_le_div_iff_of_pos_right hrR).mpr (by linarith)
  have hlower := twoCopyScore_lower_of_le_inv hr ht0 ht C hrank
  convert hlower using 1 <;> field_simp [ne_of_gt hrR] <;> ring

/-- The positive side of the strict signed separation for every nonzero
rank-at-most-`r` matrix. -/
theorem twoCopyScore_strict_separation_pos {r : ℕ} (hr : 0 < r)
    {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / ((r + 1 : ℕ) : ℝ))
    (C : Matrix (U × V) (U × V) ℂ) (hC : C ≠ 0) (hrank : C.rank ≤ r) :
    0 < twoCopyScore ((1 - ε) / (r : ℝ)) C := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hsecond : 0 < 1 - (1 - ε) / (r : ℝ) := by
    rw [sub_pos, div_lt_iff₀ hrR]
    have hrOne : (1 : ℝ) ≤ r := by exact_mod_cast hr
    nlinarith
  have hmargin :
      0 < ε * (1 - (1 - ε) / (r : ℝ)) * hsNormSq C :=
    mul_pos (mul_pos hε0 hsecond) (hsNormSq_pos hC)
  exact hmargin.trans_le
    (twoCopyScore_strict_separation_lower hr hε0 hε C hrank)

/-- The rank-`r+1` witness has the negative side of
`rem:strict-rank-gap`, again before vector normalization. -/
theorem twoCopyScore_adjacent_strict_neg {S : Finset U} {x₀ x₁ : V}
    (hx : x₀ ≠ x₁) {r : ℕ} (hr : 0 < r) (hS : S.card = r + 1)
    {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / ((r + 1 : ℕ) : ℝ)) :
    twoCopyScore ((1 - ε) / (r : ℝ)) (projWit S x₀ x₁) < 0 := by
  rw [twoCopyScore_projWit_orthogonal hx hS, hsNormSq_projWit, hS]
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hr1R : (0 : ℝ) < (r + 1 : ℕ) := by positivity
  have hcoef : (1 : ℝ) - (r + 1 : ℕ) * ((1 - ε) / (r : ℝ)) < 0 := by
    rw [sub_neg]
    have hre :
        ((r + 1 : ℕ) : ℝ) * ((1 - ε) / (r : ℝ))
          = (((r + 1 : ℕ) : ℝ) * (1 - ε)) / (r : ℝ) := by ring
    rw [hre, lt_div_iff₀ hrR]
    have hmul := (lt_div_iff₀ hr1R).mp hε
    push_cast at hmul ⊢
    nlinarith
  exact mul_neg_of_neg_of_pos hcoef (by positivity)

/-- The `a ≥ b` first branch of `thm:exact-asymmetric-score`. -/
theorem asymmetricScore_lower_left_of_le_inv {r : ℕ} (hr : 0 < r)
    {a b : ℝ} (hb0 : 0 ≤ b) (hba : b ≤ a) (ha : a ≤ 1 / (r : ℝ))
    (C : Matrix (U × V) (U × V) ℂ) (hrank : C.rank ≤ r) :
    (1 - b) * (1 - r * a) * hsNormSq C ≤ asymmetricScore a b C := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hmain := rank_r_partial_trace C r hrank
  have hU := hsNormSq_ptraceU_le C r hrank
  have htrace : Complex.normSq C.trace ≤ (r : ℝ) * hsNormSq C := by
    exact (normSq_trace_le_rank C).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hrank) (hsNormSq_nonneg C))
  have hsum : b * (hsNormSq (ptraceU C) + hsNormSq (ptraceV C))
      + (a - b) * hsNormSq (ptraceU C)
      ≤ a * r * hsNormSq C + b * (1 / (r : ℝ)) * Complex.normSq C.trace := by
    have h1 := mul_le_mul_of_nonneg_left hmain hb0
    have h2 := mul_le_mul_of_nonneg_left hU (sub_nonneg.mpr hba)
    push_cast at h1 h2
    nlinarith
  have hcoef : b * (a - 1 / (r : ℝ)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hb0 (sub_nonpos.mpr ha)
  have hcoef_use := mul_le_mul_of_nonpos_left htrace hcoef
  have hri : (r : ℝ) * (1 / (r : ℝ)) = 1 := by field_simp
  calc
    (1 - b) * (1 - r * a) * hsNormSq C
        = (1 - r * a) * hsNormSq C
          + (b * (a - 1 / (r : ℝ))) * ((r : ℝ) * hsNormSq C) := by
            field_simp [ne_of_gt hrR] <;> ring
    _ ≤ (1 - r * a) * hsNormSq C
          + b * (a - 1 / (r : ℝ)) * Complex.normSq C.trace := by
            linarith
    _ = hsNormSq C
          - (a * hsNormSq (ptraceU C) + b * hsNormSq (ptraceV C))
          + a * b * Complex.normSq C.trace
          + (a * hsNormSq (ptraceU C) + b * hsNormSq (ptraceV C)
            - (a * (r : ℝ) * hsNormSq C
              + b * (1 / (r : ℝ)) * Complex.normSq C.trace)) := by ring
    _ ≤ asymmetricScore a b C := by
      unfold asymmetricScore
      have hrewrite :
          b * (hsNormSq (ptraceU C) + hsNormSq (ptraceV C))
              + (a - b) * hsNormSq (ptraceU C)
            = a * hsNormSq (ptraceU C) + b * hsNormSq (ptraceV C) := by ring
      rw [hrewrite] at hsum
      linarith

/-- The `a ≥ b` second branch of `thm:exact-asymmetric-score`. -/
theorem asymmetricScore_lower_left_of_inv_le {r : ℕ} (hr : 0 < r)
    {a b : ℝ} (hb0 : 0 ≤ b) (hba : b ≤ a) (ha : 1 / (r : ℝ) ≤ a)
    (C : Matrix (U × V) (U × V) ℂ) (hrank : C.rank ≤ r) :
    (1 - r * a) * hsNormSq C ≤ asymmetricScore a b C := by
  have hmain := rank_r_partial_trace C r hrank
  have hU := hsNormSq_ptraceU_le C r hrank
  have hsum : b * (hsNormSq (ptraceU C) + hsNormSq (ptraceV C))
      + (a - b) * hsNormSq (ptraceU C)
      ≤ a * r * hsNormSq C + b * (1 / (r : ℝ)) * Complex.normSq C.trace := by
    have h1 := mul_le_mul_of_nonneg_left hmain hb0
    have h2 := mul_le_mul_of_nonneg_left hU (sub_nonneg.mpr hba)
    push_cast at h1 h2
    nlinarith
  have hcoef : 0 ≤ b * (a - 1 / (r : ℝ)) :=
    mul_nonneg hb0 (sub_nonneg.mpr ha)
  have htrace0 := Complex.normSq_nonneg C.trace
  calc
    (1 - r * a) * hsNormSq C
        ≤ (1 - r * a) * hsNormSq C
          + b * (a - 1 / (r : ℝ)) * Complex.normSq C.trace := by
            exact le_add_of_nonneg_right (mul_nonneg hcoef htrace0)
    _ = hsNormSq C
          - (a * (r : ℝ) * hsNormSq C
            + b * (1 / (r : ℝ)) * Complex.normSq C.trace)
          + a * b * Complex.normSq C.trace := by ring
    _ ≤ asymmetricScore a b C := by
      unfold asymmetricScore
      have hrewrite :
          b * (hsNormSq (ptraceU C) + hsNormSq (ptraceV C))
              + (a - b) * hsNormSq (ptraceU C)
            = a * hsNormSq (ptraceU C) + b * hsNormSq (ptraceV C) := by ring
      rw [hrewrite] at hsum
      linarith

/-- The symmetric `b ≥ a` first branch, using the other one-sided bound. -/
theorem asymmetricScore_lower_right_of_le_inv {r : ℕ} (hr : 0 < r)
    {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1 / (r : ℝ))
    (C : Matrix (U × V) (U × V) ℂ) (hrank : C.rank ≤ r) :
    (1 - a) * (1 - r * b) * hsNormSq C ≤ asymmetricScore a b C := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hmain := rank_r_partial_trace C r hrank
  have hV := hsNormSq_ptraceV_le C r hrank
  have htrace : Complex.normSq C.trace ≤ (r : ℝ) * hsNormSq C := by
    exact (normSq_trace_le_rank C).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hrank) (hsNormSq_nonneg C))
  have hsum : a * (hsNormSq (ptraceU C) + hsNormSq (ptraceV C))
      + (b - a) * hsNormSq (ptraceV C)
      ≤ b * r * hsNormSq C + a * (1 / (r : ℝ)) * Complex.normSq C.trace := by
    have h1 := mul_le_mul_of_nonneg_left hmain ha0
    have h2 := mul_le_mul_of_nonneg_left hV (sub_nonneg.mpr hab)
    push_cast at h1 h2
    nlinarith
  have hcoef : a * (b - 1 / (r : ℝ)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos ha0 (sub_nonpos.mpr hb)
  have hcoef_use := mul_le_mul_of_nonpos_left htrace hcoef
  have hri : (r : ℝ) * (1 / (r : ℝ)) = 1 := by field_simp
  calc
    (1 - a) * (1 - r * b) * hsNormSq C
        = (1 - r * b) * hsNormSq C
          + (a * (b - 1 / (r : ℝ))) * ((r : ℝ) * hsNormSq C) := by
            field_simp [ne_of_gt hrR] <;> ring
    _ ≤ (1 - r * b) * hsNormSq C
          + a * (b - 1 / (r : ℝ)) * Complex.normSq C.trace := by
            linarith
    _ = hsNormSq C
          - (a * hsNormSq (ptraceU C) + b * hsNormSq (ptraceV C))
          + a * b * Complex.normSq C.trace
          + (a * hsNormSq (ptraceU C) + b * hsNormSq (ptraceV C)
            - (b * (r : ℝ) * hsNormSq C
              + a * (1 / (r : ℝ)) * Complex.normSq C.trace)) := by ring
    _ ≤ asymmetricScore a b C := by
      unfold asymmetricScore
      have hrewrite :
          a * (hsNormSq (ptraceU C) + hsNormSq (ptraceV C))
              + (b - a) * hsNormSq (ptraceV C)
            = a * hsNormSq (ptraceU C) + b * hsNormSq (ptraceV C) := by ring
      rw [hrewrite] at hsum
      linarith

/-- The symmetric `b ≥ a` second branch. -/
theorem asymmetricScore_lower_right_of_inv_le {r : ℕ} (hr : 0 < r)
    {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hb : 1 / (r : ℝ) ≤ b)
    (C : Matrix (U × V) (U × V) ℂ) (hrank : C.rank ≤ r) :
    (1 - r * b) * hsNormSq C ≤ asymmetricScore a b C := by
  have hmain := rank_r_partial_trace C r hrank
  have hV := hsNormSq_ptraceV_le C r hrank
  have hsum : a * (hsNormSq (ptraceU C) + hsNormSq (ptraceV C))
      + (b - a) * hsNormSq (ptraceV C)
      ≤ b * r * hsNormSq C + a * (1 / (r : ℝ)) * Complex.normSq C.trace := by
    have h1 := mul_le_mul_of_nonneg_left hmain ha0
    have h2 := mul_le_mul_of_nonneg_left hV (sub_nonneg.mpr hab)
    push_cast at h1 h2
    nlinarith
  have hcoef : 0 ≤ a * (b - 1 / (r : ℝ)) :=
    mul_nonneg ha0 (sub_nonneg.mpr hb)
  have htrace0 := Complex.normSq_nonneg C.trace
  calc
    (1 - r * b) * hsNormSq C
        ≤ (1 - r * b) * hsNormSq C
          + a * (b - 1 / (r : ℝ)) * Complex.normSq C.trace := by
            exact le_add_of_nonneg_right (mul_nonneg hcoef htrace0)
    _ = hsNormSq C
          - (b * (r : ℝ) * hsNormSq C
            + a * (1 / (r : ℝ)) * Complex.normSq C.trace)
          + a * b * Complex.normSq C.trace := by ring
    _ ≤ asymmetricScore a b C := by
      unfold asymmetricScore
      have hrewrite :
          a * (hsNormSq (ptraceU C) + hsNormSq (ptraceV C))
              + (b - a) * hsNormSq (ptraceV C)
            = a * hsNormSq (ptraceU C) + b * hsNormSq (ptraceV C) := by ring
      rw [hrewrite] at hsum
      linarith

/-- The traceful `a ≥ b` extremizer for the asymmetric score. -/
theorem asymmetricScore_projWit_same {S : Finset U} {x : V} {r : ℕ}
    (hS : S.card = r) (a b : ℝ) :
    asymmetricScore a b (projWit S x x)
      = (1 - b) * (1 - r * a) * hsNormSq (projWit S x x) := by
  rw [asymmetricScore, hsNormSq_projWit, hsNormSq_ptraceU_projWit,
    hsNormSq_ptraceV_projWit, trace_projWit, if_pos rfl, if_pos rfl, hS,
    Complex.normSq_natCast]
  push_cast
  ring

/-- The traceless `a ≥ b` extremizer for the asymmetric score. -/
theorem asymmetricScore_projWit_orthogonal {S : Finset U} {x₀ x₁ : V}
    (hx : x₀ ≠ x₁) {r : ℕ} (hS : S.card = r) (a b : ℝ) :
    asymmetricScore a b (projWit S x₀ x₁)
      = (1 - r * a) * hsNormSq (projWit S x₀ x₁) := by
  rw [asymmetricScore, hsNormSq_projWit, hsNormSq_ptraceU_projWit,
    hsNormSq_ptraceV_projWit, trace_projWit, if_neg hx, if_neg hx, hS]
  simp
  push_cast
  ring

/-- The traceful `b ≥ a` extremizer, obtained by exchanging the factors. -/
theorem asymmetricScore_swappedProjWit_same {S : Finset V} {x : U} {r : ℕ}
    (hS : S.card = r) (a b : ℝ) :
    asymmetricScore a b (swapFactors (projWit S x x))
      = (1 - a) * (1 - r * b) * hsNormSq (swapFactors (projWit S x x)) := by
  rw [asymmetricScore_swapFactors, asymmetricScore_projWit_same hS,
    hsNormSq_swapFactors]

/-- The traceless `b ≥ a` extremizer, obtained by exchanging the factors. -/
theorem asymmetricScore_swappedProjWit_orthogonal {S : Finset V} {x₀ x₁ : U}
    (hx : x₀ ≠ x₁) {r : ℕ} (hS : S.card = r) (a b : ℝ) :
    asymmetricScore a b (swapFactors (projWit S x₀ x₁))
      = (1 - r * b) * hsNormSq (swapFactors (projWit S x₀ x₁)) := by
  rw [asymmetricScore_swapFactors, asymmetricScore_projWit_orthogonal hx hS,
    hsNormSq_swapFactors]

/-- The unrolled block-positivity condition for the asymmetric score. -/
def AsymmetricNonnegative (r : ℕ) (a b : ℝ) : Prop :=
  ∀ C : Matrix (U × V) (U × V) ℂ, C.rank ≤ r → 0 ≤ asymmetricScore a b C

/-- `cor:asymmetric-block-positive` in its genuinely rank-constrained range
`r ≤ min(dim U, dim V)`, expressed directly as the score condition. -/
theorem asymmetricNonnegative_iff {r : ℕ} (hr : 0 < r)
    (hU : r ≤ Fintype.card U) (hV : r ≤ Fintype.card V)
    (hUtwo : 2 ≤ Fintype.card U) (hVtwo : 2 ≤ Fintype.card V)
    {a b : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) :
    AsymmetricNonnegative (U := U) (V := V) r a b
      ↔ max a b ≤ 1 / (r : ℝ) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hinv_le_one : 1 / (r : ℝ) ≤ 1 := by
    rw [div_le_one hrR]
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hr))
  constructor
  · intro h
    rcases le_total b a with hba | hab
    · obtain ⟨S, -, hcard⟩ := Finset.exists_subset_card_eq
        (s := (Finset.univ : Finset U)) (by simpa using hU)
      obtain ⟨x₀, x₁, hx⟩ :=
        Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card V)
      have hrank : (projWit S x₀ x₁).rank ≤ r := by
        rw [rank_projWit, hcard]
      have hkey := h (projWit S x₀ x₁) hrank
      rw [asymmetricScore_projWit_orthogonal hx hcard, hsNormSq_projWit, hcard] at hkey
      have ha : a ≤ 1 / (r : ℝ) := by
        have hone : 0 ≤ 1 - (r : ℝ) * a :=
          nonneg_of_mul_nonneg_left hkey hrR
        rw [le_div_iff₀ hrR]
        nlinarith
      rwa [max_eq_left hba]
    · obtain ⟨S, -, hcard⟩ := Finset.exists_subset_card_eq
        (s := (Finset.univ : Finset V)) (by simpa using hV)
      obtain ⟨x₀, x₁, hx⟩ :=
        Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card U)
      have hrank : (swapFactors (projWit S x₀ x₁)).rank ≤ r := by
        rw [rank_swapFactors, rank_projWit, hcard]
      have hkey := h (swapFactors (projWit S x₀ x₁)) hrank
      rw [asymmetricScore_swappedProjWit_orthogonal hx hcard,
        hsNormSq_swapFactors, hsNormSq_projWit, hcard] at hkey
      have hb : b ≤ 1 / (r : ℝ) := by
        have hone : 0 ≤ 1 - (r : ℝ) * b :=
          nonneg_of_mul_nonneg_left hkey hrR
        rw [le_div_iff₀ hrR]
        nlinarith
      rwa [max_eq_right hab]
  · intro hm C hrank
    rcases le_total b a with hba | hab
    · have ha : a ≤ 1 / (r : ℝ) := (le_max_left _ _).trans hm
      have hrt : (r : ℝ) * a ≤ 1 := by
        have hmul := mul_le_mul_of_nonneg_left ha hrR.le
        have hri : (r : ℝ) * (1 / (r : ℝ)) = 1 := by field_simp
        rwa [hri] at hmul
      have hlower := asymmetricScore_lower_left_of_le_inv hr hb0 hba ha C hrank
      exact hlower.trans' <|
        mul_nonneg
          (mul_nonneg (sub_nonneg.mpr ((hba.trans ha).trans hinv_le_one))
            (sub_nonneg.mpr hrt))
          (hsNormSq_nonneg C)
    · have hb : b ≤ 1 / (r : ℝ) := (le_max_right _ _).trans hm
      have hrt : (r : ℝ) * b ≤ 1 := by
        have hmul := mul_le_mul_of_nonneg_left hb hrR.le
        have hri : (r : ℝ) * (1 / (r : ℝ)) = 1 := by field_simp
        rwa [hri] at hmul
      have hlower := asymmetricScore_lower_right_of_le_inv hr ha0 hab hb C hrank
      exact hlower.trans' <|
        mul_nonneg
          (mul_nonneg (sub_nonneg.mpr ((hab.trans hb).trans hinv_le_one))
            (sub_nonneg.mpr hrt))
          (hsNormSq_nonneg C)

end Scores

/-! ## Explicit Choi-form score operators -/

section ScoreOperators

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]

/-- The sum of rank-one Choi terms whose quadratic form is
`‖Tr_U C‖₂²`. -/
noncomputable def marginalChoiU :
    Matrix (((U × V) × (U × V))) (((U × V) × (U × V))) ℂ :=
  ∑ p : V × V, rankOne (gU (U := U) p.1 p.2) (gU p.1 p.2)

/-- The sum of rank-one Choi terms whose quadratic form is
`‖Tr_V C‖₂²`. -/
noncomputable def marginalChoiV :
    Matrix (((U × V) × (U × V))) (((U × V) × (U × V))) ℂ :=
  ∑ p : U × U, rankOne (gV (V := V) p.1 p.2) (gV p.1 p.2)

/-- The rank-one Choi term whose quadratic form is `|Tr C|²`. -/
noncomputable def traceChoi :
    Matrix (((U × V) × (U × V))) (((U × V) × (U × V))) ℂ :=
  rankOne (omegaVec (U := U) (V := V)) omegaVec

theorem re_qform_marginalChoiU (C : Matrix (U × V) (U × V) ℂ) :
    (qform (marginalChoiU (U := U) (V := V)) (vec C)).re
      = hsNormSq (ptraceU C) := by
  rw [marginalChoiU, qform_sum, Complex.re_sum, hsNormSq, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by
    rw [qform_rankOne, Complex.ofReal_re, inner_gU]

theorem re_qform_marginalChoiV (C : Matrix (U × V) (U × V) ℂ) :
    (qform (marginalChoiV (U := U) (V := V)) (vec C)).re
      = hsNormSq (ptraceV C) := by
  rw [marginalChoiV, qform_sum, Complex.re_sum, hsNormSq, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => by
    rw [qform_rankOne, Complex.ofReal_re, inner_gV]

theorem re_qform_traceChoi (C : Matrix (U × V) (U × V) ℂ) :
    (qform (traceChoi (U := U) (V := V)) (vec C)).re
      = Complex.normSq C.trace := by
  rw [traceChoi, qform_rankOne, Complex.ofReal_re, inner_omegaVec]

/-- The explicit Choi-form operator with quadratic form `q_{a,b}`. -/
noncomputable def asymmetricScoreOperator (a b : ℝ) :
    Matrix (((U × V) × (U × V))) (((U × V) × (U × V))) ℂ :=
  (1 : Matrix (((U × V) × (U × V))) (((U × V) × (U × V))) ℂ)
    - (a : ℂ) • marginalChoiU
    - (b : ℂ) • marginalChoiV
    + ((a * b : ℝ) : ℂ) • traceChoi

/-- `eq:q2-vectorization` and its asymmetric analogue in the coordinate
Choi rendering used by `IsBlockPositive`. -/
theorem re_qform_asymmetricScoreOperator (a b : ℝ)
    (C : Matrix (U × V) (U × V) ℂ) :
    (qform (asymmetricScoreOperator (U := U) (V := V) a b) (vec C)).re
      = asymmetricScore a b C := by
  rw [asymmetricScoreOperator, qform_add, qform_sub, qform_sub, qform_smul,
    qform_smul, qform_smul, qform_one, Complex.add_re, Complex.sub_re,
    Complex.sub_re, Complex.mul_re, Complex.mul_re, Complex.mul_re,
    re_qform_marginalChoiU, re_qform_marginalChoiV, re_qform_traceChoi]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [← hsNormSq_eq_norm_sq C]
  rfl

theorem isBlockPositive_asymmetricScoreOperator_iff (r : ℕ) (a b : ℝ) :
    IsBlockPositive r (asymmetricScoreOperator (U := U) (V := V) a b)
      ↔ AsymmetricNonnegative (U := U) (V := V) r a b := by
  constructor <;> intro h C hrank
  · simpa [re_qform_asymmetricScoreOperator] using h C hrank
  · simpa [re_qform_asymmetricScoreOperator] using h C hrank

/-- The symmetric two-copy score operator. -/
noncomputable def twoCopyScoreOperator (t : ℝ) :
    Matrix (((U × V) × (U × V))) (((U × V) × (U × V))) ℂ :=
  asymmetricScoreOperator (U := U) (V := V) t t

theorem asymmetricScore_self (t : ℝ) (C : Matrix (U × V) (U × V) ℂ) :
    asymmetricScore t t C = twoCopyScore t C := by
  unfold asymmetricScore twoCopyScore
  ring

theorem re_qform_twoCopyScoreOperator (t : ℝ)
    (C : Matrix (U × V) (U × V) ℂ) :
    (qform (twoCopyScoreOperator (U := U) (V := V) t) (vec C)).re
      = twoCopyScore t C := by
  rw [twoCopyScoreOperator, re_qform_asymmetricScoreOperator, asymmetricScore_self]

theorem isBlockPositive_twoCopyScoreOperator_iff (r : ℕ) (t : ℝ) :
    IsBlockPositive r (twoCopyScoreOperator (U := U) (V := V) t)
      ↔ TwoCopyNonnegative (U := U) (V := V) r t := by
  constructor <;> intro h C hrank
  · simpa [re_qform_twoCopyScoreOperator] using h C hrank
  · simpa [re_qform_twoCopyScoreOperator] using h C hrank

/-- `cor:two-copy-block-positive` in the range `1 ≤ r ≤ d`, in the
coordinate block-positive vocabulary. -/
theorem isBlockPositive_twoCopyScoreOperator_iff_le_inv {r : ℕ} (hr : 0 < r)
    (hU : r ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    {t : ℝ} (ht0 : 0 ≤ t) :
    IsBlockPositive r (twoCopyScoreOperator (U := U) (V := V) t)
      ↔ t ≤ 1 / (r : ℝ) := by
  rw [isBlockPositive_twoCopyScoreOperator_iff]
  exact twoCopyNonnegative_iff hr hU hV ht0

/-- `cor:asymmetric-block-positive` in the range
`1 ≤ r ≤ min(dim U, dim V)`, in the coordinate block-positive vocabulary. -/
theorem isBlockPositive_asymmetricScoreOperator_iff_max_le_inv {r : ℕ}
    (hr : 0 < r) (hU : r ≤ Fintype.card U) (hV : r ≤ Fintype.card V)
    (hUtwo : 2 ≤ Fintype.card U) (hVtwo : 2 ≤ Fintype.card V)
    {a b : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) :
    IsBlockPositive r (asymmetricScoreOperator (U := U) (V := V) a b)
      ↔ max a b ≤ 1 / (r : ℝ) := by
  rw [isBlockPositive_asymmetricScoreOperator_iff]
  exact asymmetricNonnegative_iff hr hU hV hUtwo hVtwo ha0 hb0

end ScoreOperators

/-! ## The rank-sensitive expression used in the Kronecker-sum application -/

section KroneckerCore

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]

/-- `eq:kronecker-main-use`, without normalizing `‖C‖₂ = 1`.

This is the entire rank-sensitive input to `cor:kronecker`; the remaining
step in the paper is Frobenius/Ky-Fan duality for the concrete Kronecker sum. -/
theorem centeredPartialTrace_le {k d : ℕ} (hk : 0 < k) (hd : 0 < d)
    (C : Matrix (U × V) (U × V) ℂ) (hrank : C.rank ≤ k) :
    hsNormSq (ptraceU C) + hsNormSq (ptraceV C)
        - (2 / (d : ℝ)) * Complex.normSq C.trace
      ≤ ((k : ℝ) + max 0 (1 - 2 * (k : ℝ) / d)) * hsNormSq C := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hmain := rank_r_partial_trace C k hrank
  have htrace : Complex.normSq C.trace ≤ (k : ℝ) * hsNormSq C := by
    exact (normSq_trace_le_rank C).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hrank) (hsNormSq_nonneg C))
  have hbase :
      hsNormSq (ptraceU C) + hsNormSq (ptraceV C)
          - (2 / (d : ℝ)) * Complex.normSq C.trace
        ≤ (k : ℝ) * hsNormSq C
          + (1 / (k : ℝ) - 2 / (d : ℝ)) * Complex.normSq C.trace := by
    linarith
  by_cases hc : 1 / (k : ℝ) - 2 / (d : ℝ) ≤ 0
  · have hterm : (1 / (k : ℝ) - 2 / (d : ℝ)) * Complex.normSq C.trace ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hc (Complex.normSq_nonneg _)
    have hmax : 0 ≤ max 0 (1 - 2 * (k : ℝ) / d) := le_max_left _ _
    calc
      hsNormSq (ptraceU C) + hsNormSq (ptraceV C)
          - (2 / (d : ℝ)) * Complex.normSq C.trace
          ≤ (k : ℝ) * hsNormSq C
            + (1 / (k : ℝ) - 2 / (d : ℝ)) * Complex.normSq C.trace := hbase
      _ ≤ (k : ℝ) * hsNormSq C := by linarith
      _ ≤ ((k : ℝ) + max 0 (1 - 2 * (k : ℝ) / d)) * hsNormSq C := by
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hmax) (hsNormSq_nonneg C)
  · have hcpos : 0 < 1 / (k : ℝ) - 2 / (d : ℝ) := lt_of_not_ge hc
    have hterm := mul_le_mul_of_nonneg_left htrace hcpos.le
    have hrel : 0 < 1 - 2 * (k : ℝ) / d := by
      calc
        0 < (k : ℝ) * (1 / (k : ℝ) - 2 / (d : ℝ)) :=
          mul_pos hkR hcpos
        _ = 1 - 2 * (k : ℝ) / d := by
          field_simp [ne_of_gt hkR, ne_of_gt hdR] <;> ring
    rw [max_eq_right hrel.le]
    have hki : (k : ℝ) * (1 / (k : ℝ)) = 1 := by field_simp
    calc
      hsNormSq (ptraceU C) + hsNormSq (ptraceV C)
          - (2 / (d : ℝ)) * Complex.normSq C.trace
          ≤ (k : ℝ) * hsNormSq C
            + (1 / (k : ℝ) - 2 / (d : ℝ)) * Complex.normSq C.trace := hbase
      _ ≤ (k : ℝ) * hsNormSq C
          + (1 / (k : ℝ) - 2 / (d : ℝ)) * ((k : ℝ) * hsNormSq C) := by
            linarith
      _ = ((k : ℝ) + (1 - 2 * (k : ℝ) / d)) * hsNormSq C := by
            field_simp [ne_of_gt hkR, ne_of_gt hdR] <;> ring

end KroneckerCore

end RankR
