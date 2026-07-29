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
import Mathlib.Analysis.Matrix.Order

namespace RankR

open Matrix Finset
open scoped ComplexOrder

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

omit [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] in
@[simp]
theorem swapFactors_apply (C : Matrix (V × U) (V × U) ℂ)
    (p q : U × V) : swapFactors C p q = C (p.2, p.1) (q.2, q.1) := rfl

omit [DecidableEq U] [DecidableEq V] in
@[simp]
theorem rank_swapFactors (C : Matrix (V × U) (V × U) ℂ) :
    (swapFactors C).rank = C.rank :=
  Matrix.rank_reindex (Equiv.prodComm V U) (Equiv.prodComm V U) C

omit [DecidableEq U] [DecidableEq V] in
@[simp]
theorem hsNormSq_swapFactors (C : Matrix (V × U) (V × U) ℂ) :
    hsNormSq (swapFactors C) = hsNormSq C := by
  simp only [hsNormSq, Fintype.sum_prod_type, swapFactors_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_comm

omit [DecidableEq U] [DecidableEq V] in
@[simp]
theorem trace_swapFactors (C : Matrix (V × U) (V × U) ℂ) :
    (swapFactors C).trace = C.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_prod_type, swapFactors_apply]
  rw [Finset.sum_comm]

omit [Fintype V] [DecidableEq U] [DecidableEq V] in
@[simp]
theorem ptraceU_swapFactors (C : Matrix (V × U) (V × U) ℂ) :
    ptraceU (swapFactors C) = ptraceV C := by
  ext v v'
  rfl

omit [Fintype U] [DecidableEq U] [DecidableEq V] in
@[simp]
theorem ptraceV_swapFactors (C : Matrix (V × U) (V × U) ℂ) :
    ptraceV (swapFactors C) = ptraceU C := by
  ext u u'
  rfl

omit [DecidableEq U] [DecidableEq V] in
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
            field_simp [ne_of_gt hrR]
            ring
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
  ring

/-- The traceless extremizer attains the second score branch. -/
theorem twoCopyScore_projWit_orthogonal {S : Finset U} {x₀ x₁ : V} (hx : x₀ ≠ x₁)
    {r : ℕ} (hS : S.card = r) (t : ℝ) :
    twoCopyScore t (projWit S x₀ x₁)
      = (1 - r * t) * hsNormSq (projWit S x₀ x₁) := by
  rw [twoCopyScore, hsNormSq_projWit, hsNormSq_ptraceU_projWit,
    hsNormSq_ptraceV_projWit, trace_projWit, if_neg hx, if_neg hx, hS]
  simp
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
  convert hlower using 1
  all_goals
    field_simp [ne_of_gt hrR]
    ring

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
    {ε : ℝ} (_hε0 : 0 < ε) (hε : ε < 1 / ((r + 1 : ℕ) : ℝ)) :
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
    nlinarith
  have hcoef : b * (a - 1 / (r : ℝ)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hb0 (sub_nonpos.mpr ha)
  have hcoef_use := mul_le_mul_of_nonpos_left htrace hcoef
  have hri : (r : ℝ) * (1 / (r : ℝ)) = 1 := by field_simp
  calc
    (1 - b) * (1 - r * a) * hsNormSq C
        = (1 - r * a) * hsNormSq C
          + (b * (a - 1 / (r : ℝ))) * ((r : ℝ) * hsNormSq C) := by
            field_simp [ne_of_gt hrR]
            ring
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
theorem asymmetricScore_lower_left_of_inv_le {r : ℕ} (_hr : 0 < r)
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
    nlinarith
  have hcoef : a * (b - 1 / (r : ℝ)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos ha0 (sub_nonpos.mpr hb)
  have hcoef_use := mul_le_mul_of_nonpos_left htrace hcoef
  have hri : (r : ℝ) * (1 / (r : ℝ)) = 1 := by field_simp
  calc
    (1 - a) * (1 - r * b) * hsNormSq C
        = (1 - r * b) * hsNormSq C
          + (a * (b - 1 / (r : ℝ))) * ((r : ℝ) * hsNormSq C) := by
            field_simp [ne_of_gt hrR]
            ring
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
theorem asymmetricScore_lower_right_of_inv_le {r : ℕ} (_hr : 0 < r)
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
  ring

/-- The traceless `a ≥ b` extremizer for the asymmetric score. -/
theorem asymmetricScore_projWit_orthogonal {S : Finset U} {x₀ x₁ : V}
    (hx : x₀ ≠ x₁) {r : ℕ} (hS : S.card = r) (a b : ℝ) :
    asymmetricScore a b (projWit S x₀ x₁)
      = (1 - r * a) * hsNormSq (projWit S x₀ x₁) := by
  rw [asymmetricScore, hsNormSq_projWit, hsNormSq_ptraceU_projWit,
    hsNormSq_ptraceV_projWit, trace_projWit, if_neg hx, if_neg hx, hS]
  simp
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
open scoped Kronecker

/-- The permutation from product-Choi register order
`(U_out,U_in):(V_out,V_in)` to vectorization order
`(U_out,V_out):(U_in,V_in)`. -/
def choiRegroupEquiv : (U × U) × (V × V) ≃ (U × V) × (U × V) where
  toFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  invFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- A product of two one-factor Choi matrices, in vectorization register
order. -/
def regroupChoi (A : Matrix (U × U) (U × U) ℂ)
    (B : Matrix (V × V) (V × V) ℂ) :
    Matrix (((U × V) × (U × V))) (((U × V) × (U × V))) ℂ :=
  Matrix.reindex (choiRegroupEquiv (U := U) (V := V))
    (choiRegroupEquiv (U := U) (V := V)) (A ⊗ₖ B)

omit [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] in
theorem regroupChoi_sub_left (A A' : Matrix (U × U) (U × U) ℂ)
    (B : Matrix (V × V) (V × V) ℂ) :
    regroupChoi (A - A') B = regroupChoi A B - regroupChoi A' B := by
  ext X Y
  simp [regroupChoi, Matrix.sub_apply]
  ring

omit [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] in
theorem regroupChoi_sub_right (A : Matrix (U × U) (U × U) ℂ)
    (B B' : Matrix (V × V) (V × V) ℂ) :
    regroupChoi A (B - B') = regroupChoi A B - regroupChoi A B' := by
  ext X Y
  simp [regroupChoi, Matrix.sub_apply]
  ring

omit [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] in
theorem regroupChoi_smul_left (c : ℂ) (A : Matrix (U × U) (U × U) ℂ)
    (B : Matrix (V × V) (V × V) ℂ) :
    regroupChoi (c • A) B = c • regroupChoi A B := by
  ext X Y
  simp [regroupChoi]
  ring

omit [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] in
theorem regroupChoi_smul_right (c : ℂ) (A : Matrix (U × U) (U × U) ℂ)
    (B : Matrix (V × V) (V × V) ℂ) :
    regroupChoi A (c • B) = c • regroupChoi A B := by
  ext X Y
  simp [regroupChoi]
  ring

/-- The one-factor maximally entangled vector. -/
def singleOmegaVec {T : Type*} [DecidableEq T] :
    EuclideanSpace ℂ (T × T) :=
  WithLp.toLp 2 fun p => if p.1 = p.2 then (1 : ℂ) else 0

@[simp]
theorem singleOmegaVec_apply {T : Type*} [DecidableEq T] (p : T × T) :
    singleOmegaVec p = if p.1 = p.2 then (1 : ℂ) else 0 := rfl

/-- The Choi matrix of a coordinate map, with output index first and input
index second. -/
noncomputable def mapChoi {I O : Type*} [DecidableEq I]
    (Φ : Matrix I I ℂ → Matrix O O ℂ) :
    Matrix (O × I) (O × I) ℂ :=
  Matrix.of fun p q => Φ (Matrix.single p.2 q.2 1) p.1 q.1

/-- The one-factor reduction pencil `R_{-a}(X) = Tr(X)I - aX`. -/
noncomputable def reductionMap {T : Type*} [Fintype T] [DecidableEq T]
    (a : ℝ) (X : Matrix T T ℂ) : Matrix T T ℂ :=
  X.trace • 1 - (a : ℂ) • X

/-- `|Ω_T⟩⟨Ω_T|`, the nontrivial term in the Choi matrix of a reduction
pencil. -/
noncomputable def singleOmegaChoi {T : Type*} [DecidableEq T] :
    Matrix (T × T) (T × T) ℂ :=
  rankOne (singleOmegaVec (T := T)) singleOmegaVec

/-- The Choi matrix `I - a|Ω⟩⟨Ω|` of the reduction pencil
`R_{-a}(X) = Tr(X)I - aX`. -/
noncomputable def reductionChoi {T : Type*} [DecidableEq T] (a : ℝ) :
    Matrix (T × T) (T × T) ℂ :=
  1 - (a : ℂ) • singleOmegaChoi

theorem mapChoi_reductionMap {T : Type*} [Fintype T] [DecidableEq T] (a : ℝ) :
    mapChoi (reductionMap (T := T) a) = reductionChoi (T := T) a := by
  ext p q
  obtain ⟨i, k⟩ := p
  obtain ⟨j, l⟩ := q
  by_cases hkl : k = l
  · subst l
    simp [mapChoi, reductionMap, Matrix.trace_single_eq_same, reductionChoi,
      singleOmegaChoi, rankOne, Matrix.one_apply, Matrix.single_apply, eq_comm]
    split_ifs <;> simp_all
  · simp [mapChoi, reductionMap, Matrix.trace_single_eq_of_ne k l (1 : ℂ) hkl,
      reductionChoi, singleOmegaChoi, rankOne, Matrix.one_apply,
      Matrix.single_apply, hkl, eq_comm]
    split_ifs <;> simp_all

/-- The product Choi matrix of two reduction pencils, with output and input
registers regrouped to the vectorization order used by `IsBlockPositive`. -/
noncomputable def productReductionChoi (a b : ℝ) :
    Matrix (((U × V) × (U × V))) (((U × V) × (U × V))) ℂ :=
  regroupChoi (reductionChoi (T := U) a) (reductionChoi (T := V) b)

/-- The product object is literally the regrouped tensor product of the Choi
matrices of the two coordinate reduction maps. -/
theorem productReductionChoi_eq_regroup_mapChoi (a b : ℝ) :
    productReductionChoi (U := U) (V := V) a b
      = regroupChoi (mapChoi (reductionMap (T := U) a))
          (mapChoi (reductionMap (T := V) b)) := by
  rw [mapChoi_reductionMap, mapChoi_reductionMap]
  rfl

theorem inner_singleOmegaVec {T : Type*} [Fintype T] [DecidableEq T]
    (C : Matrix T T ℂ) :
    inner ℂ (singleOmegaVec (T := T)) (vec C) = C.trace := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type, Matrix.trace]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.diag_apply]
  have h : ∀ y : T,
      (inner ℂ (singleOmegaVec (T := T) (x, y)) (vec C (x, y)) : ℂ)
        = if x = y then C x y else 0 := by
    intro y
    rw [RCLike.inner_apply', singleOmegaVec_apply, vec_apply]
    by_cases hxy : x = y <;> simp [hxy]
  rw [Finset.sum_congr rfl fun y _ => h y, Finset.sum_ite_eq]
  simp

theorem qform_reductionChoi {T : Type*} [Fintype T] [DecidableEq T]
    (a : ℝ) (C : Matrix T T ℂ) :
    qform (reductionChoi (T := T) a) (vec C)
      = ((hsNormSq C - a * Complex.normSq C.trace : ℝ) : ℂ) := by
  rw [reductionChoi, qform_sub, qform_smul, qform_one, singleOmegaChoi,
    qform_rankOne, inner_singleOmegaVec, hsNormSq_eq_norm_sq]
  norm_cast

/-- The reduction witness `I - |Ω⟩⟨Ω|/r` is `r`-block-positive.

This is the one-factor rank--trace inequality in witness form. -/
theorem reductionChoi_inv_isBlockPositive {T : Type*} [Fintype T]
    [DecidableEq T] {r : ℕ} (hr : 0 < r) :
    IsBlockPositive r (reductionChoi (T := T) (1 / (r : ℝ))) := by
  intro C hCrank
  rw [qform_reductionChoi, Complex.ofReal_re, sub_nonneg]
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have htrace :
      Complex.normSq C.trace ≤ (r : ℝ) * hsNormSq C :=
    (normSq_trace_le_rank C).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hCrank)
        (hsNormSq_nonneg C))
  rw [one_div_mul_eq_div, div_le_iff₀ hrR]
  nlinarith

theorem reductionChoi_isHermitian {T : Type*} [DecidableEq T] (a : ℝ) :
    (reductionChoi (T := T) a).IsHermitian := by
  rw [Matrix.IsHermitian]
  simp [reductionChoi, singleOmegaChoi, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    rankOne_conjTranspose]

/-- The reduction-pencil Choi matrix is positive semidefinite in its
completely-positive range `0 ≤ a ≤ 1 / dim(T)`. -/
theorem reductionChoi_posSemidef {T : Type*} [Fintype T] [DecidableEq T]
    {a : ℝ} (ha0 : 0 ≤ a) (hT : 0 < Fintype.card T)
    (ha : a ≤ 1 / (Fintype.card T : ℝ)) :
    (reductionChoi (T := T) a).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (reductionChoi_isHermitian a) ?_
  intro x
  let C : Matrix T T ℂ := Matrix.of fun i j => x (i, j)
  have hvec : vec C = WithLp.toLp 2 x := rfl
  have htrace_rank := normSq_trace_le_rank C
  have hrank : (C.rank : ℝ) ≤ Fintype.card T := by
    exact_mod_cast Matrix.rank_le_card_width C
  have hnorm := hsNormSq_nonneg C
  have htrace :
      Complex.normSq C.trace ≤ (Fintype.card T : ℝ) * hsNormSq C :=
    htrace_rank.trans (mul_le_mul_of_nonneg_right hrank hnorm)
  have hcard : (0 : ℝ) < Fintype.card T := by exact_mod_cast hT
  have hacard : a * (Fintype.card T : ℝ) ≤ 1 :=
    (le_div_iff₀ hcard).mp ha
  have hatrace := mul_le_mul_of_nonneg_left htrace ha0
  have hacard_norm := mul_le_mul_of_nonneg_right hacard hnorm
  have hreal : 0 ≤ hsNormSq C - a * Complex.normSq C.trace := by
    rw [sub_nonneg]
    calc
      a * Complex.normSq C.trace
          ≤ a * ((Fintype.card T : ℝ) * hsNormSq C) := hatrace
      _ = (a * (Fintype.card T : ℝ)) * hsNormSq C := by ring
      _ ≤ 1 * hsNormSq C := hacard_norm
      _ = hsNormSq C := one_mul _
  have hdot :
      star x ⬝ᵥ (reductionChoi (T := T) a *ᵥ x)
        = qform (reductionChoi (T := T) a) (WithLp.toLp 2 x) := by
    simp [qform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [hdot, ← hvec, qform_reductionChoi]
  exact (RCLike.ofReal_nonneg (K := ℂ)).mpr hreal

/-- A positive semidefinite Choi matrix is block-positive at every level. -/
theorem isBlockPositive_of_posSemidef {W : Type*} [Fintype W]
    {M : Matrix (W × W) (W × W) ℂ} (hM : M.PosSemidef) (r : ℕ) :
    IsBlockPositive r M := by
  intro C _
  have hq : 0 ≤ qform M (vec C) := by
    have hdot := hM.dotProduct_mulVec_nonneg (vec C)
    simpa [qform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc] using hdot
  exact (Complex.nonneg_iff.mp hq).1

/-- In the completely-positive parameter range, the regrouped product Choi
matrix is positive semidefinite and hence block-positive at every rank. -/
theorem productReductionChoi_posSemidef
    {a b : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (hU : 0 < Fintype.card U) (hV : 0 < Fintype.card V)
    (ha : a ≤ 1 / (Fintype.card U : ℝ))
    (hb : b ≤ 1 / (Fintype.card V : ℝ)) :
    (productReductionChoi (U := U) (V := V) a b).PosSemidef := by
  rw [productReductionChoi, regroupChoi, Matrix.reindex_apply]
  exact (reductionChoi_posSemidef ha0 hU ha).kronecker
    (reductionChoi_posSemidef hb0 hV hb) |>.submatrix _

omit [Fintype U] [Fintype V] in
theorem productReductionChoi_isHermitian (a b : ℝ) :
    (productReductionChoi (U := U) (V := V) a b).IsHermitian := by
  have hkr :
      ((reductionChoi (T := U) a) ⊗ₖ (reductionChoi (T := V) b)).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_kronecker,
      (reductionChoi_isHermitian a).eq, (reductionChoi_isHermitian b).eq]
  exact hkr.reindex (choiRegroupEquiv (U := U) (V := V))

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

private theorem sum_pair_indicator {T : Type*} [Fintype T] [DecidableEq T]
    (a b c d : T) :
    ∑ p : T × T,
        (if a = p.1 ∧ b = p.2 then
          if c = p.1 ∧ d = p.2 then (1 : ℂ) else 0
        else 0)
      = if a = c ∧ b = d then 1 else 0 := by
  rw [Fintype.sum_eq_single (a, b) (fun p hp => by
    have hne : ¬(a = p.1 ∧ b = p.2) := by
      rintro ⟨h₁, h₂⟩
      exact hp (Prod.ext h₁.symm h₂.symm)
    simp [hne])]
  simp [eq_comm]

omit [Fintype U] in
private theorem marginalChoiU_apply (u u' w w' : U) (v v' x x' : V) :
    marginalChoiU (U := U) (V := V) ((u, v), (u', v')) ((w, x), (w', x'))
      = if u = u' ∧ w = w' ∧ v = x ∧ v' = x' then 1 else 0 := by
  simp only [marginalChoiU, Matrix.sum_apply, rankOne, Matrix.of_apply, gU_apply]
  by_cases hu : u = u' <;> by_cases hw : w = w'
  · subst u'
    subst w'
    simpa [eq_comm] using sum_pair_indicator x x' v v'
  · simp [hu, hw]
  · simp [hu, hw]
  · simp [hu, hw]

omit [Fintype V] in
private theorem marginalChoiV_apply (u u' w w' : U) (v v' x x' : V) :
    marginalChoiV (U := U) (V := V) ((u, v), (u', v')) ((w, x), (w', x'))
      = if v = v' ∧ x = x' ∧ u = w ∧ u' = w' then 1 else 0 := by
  simp only [marginalChoiV, Matrix.sum_apply, rankOne, Matrix.of_apply, gV_apply]
  by_cases hv : v = v' <;> by_cases hx : x = x'
  · subst v'
    subst x'
    simpa [eq_comm] using sum_pair_indicator w w' u u'
  · simp [hv, hx]
  · simp [hv, hx]
  · simp [hv, hx]

omit [Fintype U] in
theorem regroupChoi_singleOmega_one :
    regroupChoi (singleOmegaChoi (T := U))
        (1 : Matrix (V × V) (V × V) ℂ)
      = marginalChoiU (U := U) (V := V) := by
  ext X Y
  obtain ⟨⟨u, v⟩, u', v'⟩ := X
  obtain ⟨⟨w, x⟩, w', x'⟩ := Y
  simp [regroupChoi, choiRegroupEquiv, singleOmegaChoi, marginalChoiU_apply,
    rankOne, Matrix.one_apply, Prod.ext_iff]
  aesop

omit [Fintype V] in
theorem regroupChoi_one_singleOmega :
    regroupChoi (1 : Matrix (U × U) (U × U) ℂ)
        (singleOmegaChoi (T := V))
      = marginalChoiV (U := U) (V := V) := by
  ext X Y
  obtain ⟨⟨u, v⟩, u', v'⟩ := X
  obtain ⟨⟨w, x⟩, w', x'⟩ := Y
  simp [regroupChoi, choiRegroupEquiv, singleOmegaChoi, marginalChoiV_apply,
    rankOne, Matrix.one_apply, Prod.ext_iff]
  aesop

omit [Fintype U] [Fintype V] in
theorem regroupChoi_singleOmega_singleOmega :
    regroupChoi (singleOmegaChoi (T := U)) (singleOmegaChoi (T := V))
      = traceChoi (U := U) (V := V) := by
  ext X Y
  obtain ⟨⟨u, v⟩, u', v'⟩ := X
  obtain ⟨⟨w, x⟩, w', x'⟩ := Y
  simp [regroupChoi, choiRegroupEquiv, singleOmegaChoi, traceChoi,
    rankOne, omegaVec]
  split_ifs <;> simp_all

omit [Fintype U] [Fintype V] in
theorem regroupChoi_one_one :
    regroupChoi (1 : Matrix (U × U) (U × U) ℂ)
        (1 : Matrix (V × V) (V × V) ℂ)
      = 1 := by
  ext X Y
  obtain ⟨⟨u, v⟩, u', v'⟩ := X
  obtain ⟨⟨w, x⟩, w', x'⟩ := Y
  simp [regroupChoi, choiRegroupEquiv, Matrix.one_apply, Prod.ext_iff]
  split_ifs <;> simp_all

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

/-- The coordinate score operator is exactly the regrouped tensor product
`J(R_{-a}) ⊗ J(R_{-b})`, not merely an operator with the same tested quadratic
form. -/
theorem productReductionChoi_eq_asymmetricScoreOperator (a b : ℝ) :
    productReductionChoi (U := U) (V := V) a b
      = asymmetricScoreOperator (U := U) (V := V) a b := by
  simp only [productReductionChoi, reductionChoi, regroupChoi_sub_left,
    regroupChoi_sub_right, regroupChoi_smul_left, regroupChoi_smul_right,
    regroupChoi_one_one, regroupChoi_singleOmega_one,
    regroupChoi_one_singleOmega, regroupChoi_singleOmega_singleOmega]
  ext X Y
  simp [asymmetricScoreOperator]
  ring

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

theorem productReductionChoi_self_eq_twoCopyScoreOperator (t : ℝ) :
    productReductionChoi (U := U) (V := V) t t
      = twoCopyScoreOperator (U := U) (V := V) t := by
  rw [productReductionChoi_eq_asymmetricScoreOperator]
  rfl

omit [DecidableEq U] [DecidableEq V] in
theorem asymmetricScore_self (t : ℝ) (C : Matrix (U × V) (U × V) ℂ) :
    asymmetricScore t t C = twoCopyScore t C := by
  unfold asymmetricScore twoCopyScore
  ring

theorem re_qform_twoCopyScoreOperator (t : ℝ)
    (C : Matrix (U × V) (U × V) ℂ) :
    (qform (twoCopyScoreOperator (U := U) (V := V) t) (vec C)).re
      = twoCopyScore t C := by
  rw [twoCopyScoreOperator, re_qform_asymmetricScoreOperator, asymmetricScore_self]

/-- The normalized adjacent-rank witness used in
`cor:adjacent-rank-gap` and `rem:strict-rank-gap`.  Its expectation is
the entire normalized score `1 - (r+1)t`, not only either specialization
used in the manuscript. -/
theorem exists_unit_pureSchmidtRank_adjacent_score
    {T : Type*} [Fintype T] [DecidableEq T] {r : ℕ}
    (hr : 0 < r) (hrT : r < Fintype.card T) (t : ℝ) :
    ∃ ψ : EuclideanSpace ℂ ((T × T) × (T × T)),
      ‖ψ‖ = 1 ∧
      pureSchmidtRank ψ = r + 1 ∧
      (qform
        (productReductionChoi (U := T) (V := T)
          t t) ψ).re =
        1 - (r + 1 : ℕ) * t := by
  have hrT' : r + 1 ≤ Fintype.card T := by omega
  obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset T)) (by
      simpa only [Finset.card_univ] using hrT')
  obtain ⟨x₀, x₁, hx⟩ :=
    Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card T)
  let C : Matrix (T × T) (T × T) ℂ := projWit S x₀ x₁
  let z : EuclideanSpace ℂ ((T × T) × (T × T)) := vec C
  have hC : C ≠ 0 := by
    intro hzero
    have hnorm := hsNormSq_projWit (S := S) x₀ x₁
    change projWit S x₀ x₁ = 0 at hzero
    rw [hzero] at hnorm
    have hcardpos : (0 : ℝ) < S.card := by
      rw [hS]
      positivity
    have hcardzero : (0 : ℝ) = S.card := by
      simpa [hsNormSq] using hnorm
    linarith
  have hz : z ≠ 0 := by
    intro hzero
    apply hC
    ext i j
    have happ := congrFun (congrArg WithLp.ofLp hzero) (i, j)
    simpa [z] using happ
  have hznorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hc : (‖z‖⁻¹ : ℂ) ≠ 0 := by
    exact_mod_cast inv_ne_zero hznorm.ne'
  refine ⟨(‖z‖⁻¹ : ℂ) • z, ?_, ?_, ?_⟩
  · rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hznorm, inv_mul_cancel₀ hznorm.ne']
  · rw [pureSchmidtRank_smul_of_ne_zero _ hc]
    change C.rank = r + 1
    rw [show C = projWit S x₀ x₁ from rfl, rank_projWit, hS]
  · calc
      (qform
          (productReductionChoi (U := T) (V := T)
            t t)
          ((‖z‖⁻¹ : ℂ) • z)).re =
          Complex.normSq (‖z‖⁻¹ : ℂ) *
            (qform
              (productReductionChoi (U := T) (V := T)
                t t) z).re := by
        rw [qform_smul_vec, Complex.mul_re]
        simp
      _ = Complex.normSq (‖z‖⁻¹ : ℂ) *
          twoCopyScore t C := by
        rw [productReductionChoi_self_eq_twoCopyScoreOperator,
          show z = vec C from rfl, re_qform_twoCopyScoreOperator]
      _ = 1 - (r + 1 : ℕ) * t := by
        rw [twoCopyScore_projWit_orthogonal hx hS,
          Complex.normSq_inv, Complex.normSq_ofReal,
          hsNormSq_eq_norm_sq]
        simp only [z, C]
        field_simp [hznorm.ne']
        rw [mul_div_cancel_left₀ _ (by simpa [z, C] using hznorm.ne')]

/-- The normalized endpoint witness asserted in `cor:adjacent-rank-gap`.
When `0 < r < dim T`, the reduction-product Choi operator at `t = 1/r`
has a unit vector of pure Schmidt rank exactly `r+1` and expectation
exactly `-1/r`. -/
theorem exists_unit_pureSchmidtRank_adjacent_endpoint
    {T : Type*} [Fintype T] [DecidableEq T] {r : ℕ}
    (hr : 0 < r) (hrT : r < Fintype.card T) :
    ∃ ψ : EuclideanSpace ℂ ((T × T) × (T × T)),
      ‖ψ‖ = 1 ∧
      pureSchmidtRank ψ = r + 1 ∧
      (qform
        (productReductionChoi (U := T) (V := T)
          (1 / (r : ℝ)) (1 / (r : ℝ))) ψ).re =
        -(1 / (r : ℝ)) := by
  obtain ⟨ψ, hψ, hrank, hscore⟩ :=
    exists_unit_pureSchmidtRank_adjacent_score hr hrT (1 / (r : ℝ))
  refine ⟨ψ, hψ, hrank, hscore.trans ?_⟩
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  push_cast
  field_simp [ne_of_gt hrR]
  ring

/-- The uniform margin in `rem:strict-rank-gap`, stated directly for pure
vectors of Schmidt rank at most `r`. -/
theorem re_qform_productReductionChoi_strict_lower_of_pureSchmidtRank_le
    {T : Type*} [Fintype T] [DecidableEq T] {r : ℕ}
    (hr : 0 < r) {ε : ℝ}
    (hε0 : 0 < ε) (hε : ε < 1 / ((r + 1 : ℕ) : ℝ))
    (ψ : EuclideanSpace ℂ ((T × T) × (T × T)))
    (hrank : pureSchmidtRank ψ ≤ r) :
    ε * (1 - (1 - ε) / (r : ℝ)) * ‖ψ‖ ^ 2 ≤
      (qform
        (productReductionChoi (U := T) (V := T)
          ((1 - ε) / (r : ℝ)) ((1 - ε) / (r : ℝ))) ψ).re := by
  have hscore :=
    twoCopyScore_strict_separation_lower hr hε0 hε
      (unvec ψ) (by simpa [pureSchmidtRank] using hrank)
  rw [hsNormSq_eq_norm_sq, vec_unvec,
    ← re_qform_twoCopyScoreOperator, vec_unvec,
    ← productReductionChoi_self_eq_twoCopyScoreOperator] at hscore
  exact hscore

/-- The positive side of `rem:strict-rank-gap`, stated directly for
nonzero pure vectors of Schmidt rank at most `r`. -/
theorem re_qform_productReductionChoi_strict_pos_of_pureSchmidtRank_le
    {T : Type*} [Fintype T] [DecidableEq T] {r : ℕ}
    (hr : 0 < r) {ε : ℝ}
    (hε0 : 0 < ε) (hε : ε < 1 / ((r + 1 : ℕ) : ℝ))
    (ψ : EuclideanSpace ℂ ((T × T) × (T × T)))
    (hψ : ψ ≠ 0) (hrank : pureSchmidtRank ψ ≤ r) :
    0 <
      (qform
        (productReductionChoi (U := T) (V := T)
          ((1 - ε) / (r : ℝ)) ((1 - ε) / (r : ℝ))) ψ).re := by
  have hC : unvec ψ ≠ 0 := by
    intro hzero
    apply hψ
    rw [← vec_unvec ψ, hzero, vec_zero]
  have hscore :=
    twoCopyScore_strict_separation_pos hr hε0 hε
      (unvec ψ) hC (by simpa [pureSchmidtRank] using hrank)
  rw [← re_qform_twoCopyScoreOperator, vec_unvec,
    ← productReductionChoi_self_eq_twoCopyScoreOperator] at hscore
  exact hscore

/-- The negative side of `rem:strict-rank-gap`, including the unit-vector
normalization and exact adjacent pure Schmidt rank. -/
theorem exists_unit_pureSchmidtRank_adjacent_strict_neg
    {T : Type*} [Fintype T] [DecidableEq T] {r : ℕ}
    (hr : 0 < r) (hrT : r < Fintype.card T) {ε : ℝ}
    (_hε0 : 0 < ε) (hε : ε < 1 / ((r + 1 : ℕ) : ℝ)) :
    ∃ ψ : EuclideanSpace ℂ ((T × T) × (T × T)),
      ‖ψ‖ = 1 ∧
      pureSchmidtRank ψ = r + 1 ∧
      (qform
        (productReductionChoi (U := T) (V := T)
          ((1 - ε) / (r : ℝ)) ((1 - ε) / (r : ℝ))) ψ).re < 0 := by
  obtain ⟨ψ, hψ, hrank, hscore⟩ :=
    exists_unit_pureSchmidtRank_adjacent_score
      hr hrT ((1 - ε) / (r : ℝ))
  refine ⟨ψ, hψ, hrank, ?_⟩
  rw [hscore]
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hr1R : (0 : ℝ) < (r + 1 : ℕ) := by positivity
  have hε' : ε * ((r + 1 : ℕ) : ℝ) < 1 :=
    (lt_div_iff₀ hr1R).mp hε
  norm_num [Nat.cast_add, Nat.cast_one] at hε' ⊢
  rw [show ((r : ℝ) + 1) * ((1 - ε) / r) =
    (((r : ℝ) + 1) * (1 - ε)) / r by ring]
  rw [lt_div_iff₀ hrR]
  nlinarith

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

/-- The asymmetric threshold in the rank-constrained range, stated for the
actual regrouped tensor product of the two one-factor Choi matrices. -/
theorem isBlockPositive_productReductionChoi_iff_max_le_inv {r : ℕ}
    (hr : 0 < r) (hU : r ≤ Fintype.card U) (hV : r ≤ Fintype.card V)
    (hUtwo : 2 ≤ Fintype.card U) (hVtwo : 2 ≤ Fintype.card V)
    {a b : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) :
    IsBlockPositive r (productReductionChoi (U := U) (V := V) a b)
      ↔ max a b ≤ 1 / (r : ℝ) := by
  rw [productReductionChoi_eq_asymmetricScoreOperator]
  exact isBlockPositive_asymmetricScoreOperator_iff_max_le_inv
    hr hU hV hUtwo hVtwo ha0 hb0

/-- Once the tested rank reaches the local dimension, complete positivity of
both factors gives sufficiency at `1 / dim`, while the rank-`dim` witness gives
necessity. -/
theorem isBlockPositive_productReductionChoi_iff_max_le_inv_card
    {T : Type*} [Fintype T] [DecidableEq T] {r : ℕ}
    (hTtwo : 2 ≤ Fintype.card T) (hTr : Fintype.card T ≤ r)
    {a b : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) :
    IsBlockPositive r (productReductionChoi (U := T) (V := T) a b)
      ↔ max a b ≤ 1 / (Fintype.card T : ℝ) := by
  have hTpos : 0 < Fintype.card T := by omega
  constructor
  · intro h
    have hdim :
        IsBlockPositive (Fintype.card T)
          (productReductionChoi (U := T) (V := T) a b) := by
      intro C hrank
      exact h C (hrank.trans hTr)
    rw [productReductionChoi_eq_asymmetricScoreOperator] at hdim
    exact (isBlockPositive_asymmetricScoreOperator_iff_max_le_inv
      hTpos le_rfl le_rfl hTtwo hTtwo ha0 hb0).mp hdim
  · intro hmax
    have ha : a ≤ 1 / (Fintype.card T : ℝ) := (le_max_left a b).trans hmax
    have hb : b ≤ 1 / (Fintype.card T : ℝ) := (le_max_right a b).trans hmax
    exact isBlockPositive_of_posSemidef
      (productReductionChoi_posSemidef ha0 hb0 hTpos hTpos ha hb) r

/-- `cor:asymmetric-block-positive`, including the completely-positive
continuation past the local dimension.  The theorem is stated for every
positive `r`; the manuscript only needs `r ≤ d²`. -/
theorem isBlockPositive_productReductionChoi_iff_max_le_inv_min
    {T : Type*} [Fintype T] [DecidableEq T] {r : ℕ}
    (hr : 0 < r) (hTtwo : 2 ≤ Fintype.card T)
    {a b : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) :
    IsBlockPositive r (productReductionChoi (U := T) (V := T) a b)
      ↔ max a b ≤ 1 / (min r (Fintype.card T) : ℝ) := by
  by_cases hrT : r ≤ Fintype.card T
  · have hrTR : (r : ℝ) ≤ Fintype.card T := by exact_mod_cast hrT
    rw [min_eq_left hrTR]
    exact isBlockPositive_productReductionChoi_iff_max_le_inv
      hr hrT hrT hTtwo hTtwo ha0 hb0
  · have hTr : Fintype.card T ≤ r := by omega
    have hTrR : (Fintype.card T : ℝ) ≤ r := by exact_mod_cast hTr
    rw [min_eq_right hTrR]
    exact isBlockPositive_productReductionChoi_iff_max_le_inv_card
      hTtwo hTr ha0 hb0

/-- `cor:two-copy-block-positive`, for the regrouped tensor square and all
positive ranks. -/
theorem isBlockPositive_productReductionChoi_self_iff_le_inv_min
    {T : Type*} [Fintype T] [DecidableEq T] {r : ℕ}
    (hr : 0 < r) (hTtwo : 2 ≤ Fintype.card T)
    {t : ℝ} (ht0 : 0 ≤ t) :
    IsBlockPositive r (productReductionChoi (U := T) (V := T) t t)
      ↔ t ≤ 1 / (min r (Fintype.card T) : ℝ) := by
  simpa using (isBlockPositive_productReductionChoi_iff_max_le_inv_min
    (T := T) hr hTtwo ht0 ht0)

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
          field_simp [ne_of_gt hkR, ne_of_gt hdR]
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
            field_simp [ne_of_gt hkR, ne_of_gt hdR]

end KroneckerCore

end RankR
