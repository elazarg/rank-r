/-
Scalar core of `paper/derivation-schmidt-staircase.tex`.

The operator-theoretic part of that note needs isotropic states, Haar twirls and
mixed-state Schmidt number, none of which is present in the development.  This
file isolates the exact rational identities that determine the threshold and
the boundary decomposition.  Thus a future semantic layer cannot silently
change the constants while implementing the state-level argument.
-/
import Mathlib

namespace RankR

/-- The white-noise expectation `γ_k`. -/
noncomputable def staircaseGamma (m n k : ℝ) : ℝ :=
  k * (1 - 1 / (k * m)) * (1 - 1 / (k * n))

/-- The common denominator `D_k`. -/
def staircaseD (m n s k : ℝ) : ℝ :=
  (k * m - 1) * (k * n - 1) + k * m * n * (s - k)

/-- The exact staircase threshold `p_k`. -/
noncomputable def staircaseP (m n s k : ℝ) : ℝ :=
  (k * m - 1) * (k * n - 1) / staircaseD m n s k

/-- The mixing coefficient in the boundary decomposition. -/
noncomputable def staircaseAlpha (m n s k : ℝ) : ℝ :=
  m * (s - k) / staircaseD m n s k

theorem staircaseGamma_eq_fraction {m n k : ℝ}
    (hm : m ≠ 0) (hn : n ≠ 0) (hk : k ≠ 0) :
    staircaseGamma m n k = (k * m - 1) * (k * n - 1) / (k * m * n) := by
  unfold staircaseGamma
  field_simp

theorem staircaseGamma_eq_expanded {m n k : ℝ}
    (hm : m ≠ 0) (hn : n ≠ 0) (hk : k ≠ 0) :
    staircaseGamma m n k = k - 1 / m - 1 / n + 1 / (k * m * n) := by
  unfold staircaseGamma
  field_simp
  ring

private theorem staircase_factors_pos {m n s k : ℝ}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (hk : 1 ≤ k) (hks : k < s) :
    0 < k * m - 1 ∧ 0 < k * n - 1 ∧ 0 < m * (s - k) ∧
      0 < k * m * n * (s - k) := by
  have hk0 : 0 ≤ k := le_trans (by norm_num) hk
  have hkm : 2 ≤ k * m := by
    calc
      2 = 1 * 2 := by ring
      _ ≤ k * m := mul_le_mul hk hm (by norm_num) hk0
  have hkn : 2 ≤ k * n := by
    calc
      2 = 1 * 2 := by ring
      _ ≤ k * n := mul_le_mul hk hn (by norm_num) hk0
  have hm0 : 0 < m := lt_of_lt_of_le (by norm_num) hm
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hkpos : 0 < k := lt_of_lt_of_le (by norm_num) hk
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · exact mul_pos hm0 (sub_pos.mpr hks)
  · positivity

theorem staircaseD_pos {m n s k : ℝ}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (hk : 1 ≤ k) (hks : k < s) :
    0 < staircaseD m n s k := by
  obtain ⟨hkm, hkn, -, hnoise⟩ := staircase_factors_pos hm hn hk hks
  unfold staircaseD
  exact add_pos (mul_pos hkm hkn) hnoise

theorem staircaseD_eq_gamma {m n s k : ℝ}
    (hm : m ≠ 0) (hn : n ≠ 0) (hk : k ≠ 0) :
    staircaseD m n s k = k * m * n * (staircaseGamma m n k + s - k) := by
  rw [staircaseGamma_eq_fraction hm hn hk]
  unfold staircaseD
  field_simp
  ring

theorem staircaseGamma_pos {m n s k : ℝ}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (hk : 1 ≤ k) (hks : k < s) :
    0 < staircaseGamma m n k := by
  obtain ⟨hkm, hkn, -, -⟩ := staircase_factors_pos hm hn hk hks
  have hmpos : 0 < m := lt_of_lt_of_le (by norm_num) hm
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hkpos : 0 < k := lt_of_lt_of_le (by norm_num) hk
  rw [staircaseGamma_eq_fraction (ne_of_gt hmpos) (ne_of_gt hnpos) (ne_of_gt hkpos)]
  exact div_pos (mul_pos hkm hkn) (by positivity)

theorem staircaseP_eq_gamma_ratio {m n s k : ℝ}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (hk : 1 ≤ k) (hks : k < s) :
    staircaseP m n s k
      = staircaseGamma m n k / (staircaseGamma m n k + s - k) := by
  have hm0 : m ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hm)
  have hn0 : n ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hn)
  have hk0 : k ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hk)
  have hD := staircaseD_pos hm hn hk hks
  have hγ := staircaseGamma_pos hm hn hk hks
  have hsum : 0 < staircaseGamma m n k + s - k := by linarith
  rw [staircaseP]
  rw [staircaseD_eq_gamma hm0 hn0 hk0]
  rw [staircaseGamma_eq_fraction hm0 hn0 hk0]
  field_simp [hm0, hn0, hk0, ne_of_gt hsum]

/-- Both formulas for `α_k` in `eq:Dk-alphak` agree. -/
theorem staircaseAlpha_eq {m n s k : ℝ}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (hk : 1 ≤ k) (hks : k < s) :
    staircaseAlpha m n s k = (1 - staircaseP m n s k) / (k * n) := by
  have hkpos : 0 < k := lt_of_lt_of_le (by norm_num) hk
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hD := staircaseD_pos hm hn hk hks
  rw [staircaseAlpha, staircaseP]
  field_simp [ne_of_gt hkpos, ne_of_gt hnpos, ne_of_gt hD]
  unfold staircaseD
  ring

/-- The boundary coefficient is genuinely convex. -/
theorem staircaseAlpha_mem_Ioo {m n s k : ℝ}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (hk : 1 ≤ k) (hks : k < s) :
    staircaseAlpha m n s k ∈ Set.Ioo 0 1 := by
  obtain ⟨hkm, hkn, hnum, -⟩ := staircase_factors_pos hm hn hk hks
  have hD := staircaseD_pos hm hn hk hks
  constructor
  · exact div_pos hnum hD
  · rw [staircaseAlpha, div_lt_one hD]
    have hgap :
        staircaseD m n s k - m * (s - k)
          = (k * m - 1) * (k * n - 1)
            + m * (s - k) * (k * n - 1) := by
      unfold staircaseD
      ring
    rw [← sub_pos]
    rw [hgap]
    exact add_pos (mul_pos hkm hkn) (mul_pos hnum hkn)

/-- The three scalar moment identities proving the boundary decomposition. -/
theorem staircase_boundary_moments {m n s k : ℝ}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (hk : 1 ≤ k) (hks : k < s) :
    let p := staircaseP m n s k
    let α := staircaseAlpha m n s k
    p * (s / m) + (1 - p) / m ^ 2
        = (1 - α) * (k / m) + α / m ^ 2
      ∧ (1 - p) / n ^ 2 = α * (k / n)
      ∧ (1 - p) / (m ^ 2 * n ^ 2) = α * (k / (m ^ 2 * n)) := by
  dsimp
  have hmpos : 0 < m := lt_of_lt_of_le (by norm_num) hm
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hkpos : 0 < k := lt_of_lt_of_le (by norm_num) hk
  have hD := staircaseD_pos hm hn hk hks
  rw [staircaseP, staircaseAlpha]
  constructor
  · field_simp [ne_of_gt hmpos, ne_of_gt hnpos, ne_of_gt hkpos, ne_of_gt hD]
    unfold staircaseD
    ring
  constructor
  · field_simp [ne_of_gt hmpos, ne_of_gt hnpos, ne_of_gt hkpos, ne_of_gt hD]
    unfold staircaseD
    ring
  · field_simp [ne_of_gt hmpos, ne_of_gt hnpos, ne_of_gt hkpos, ne_of_gt hD]
    unfold staircaseD
    ring

/-- The affine witness expectation crosses zero exactly at `γ/(γ+c)`. -/
theorem affine_threshold_iff {γ c p : ℝ} (hγ : 0 < γ) (hc : 0 < c) :
    (1 - p) * γ - p * c < 0 ↔ γ / (γ + c) < p := by
  rw [div_lt_iff₀ (add_pos hγ hc)]
  constructor <;> intro h <;> nlinarith

theorem staircaseGamma_succ_sub {m n k : ℝ}
    (hm : m ≠ 0) (hn : n ≠ 0) (hk : k ≠ 0) (hk1 : k + 1 ≠ 0) :
    staircaseGamma m n (k + 1) - staircaseGamma m n k
      = 1 - 1 / (k * (k + 1) * m * n) := by
  rw [staircaseGamma_eq_expanded hm hn hk1,
    staircaseGamma_eq_expanded hm hn hk]
  field_simp
  ring

private theorem ratio_lt_ratio_of_lt_of_gt {x y c d : ℝ}
    (hx : 0 < x) (hxy : x < y) (hd : 0 < d) (hdc : d < c) :
    x / (x + c) < y / (y + d) := by
  have hy : 0 < y := hx.trans hxy
  have hc : 0 < c := hd.trans hdc
  rw [div_lt_div_iff₀ (add_pos hx hc) (add_pos hy hd)]
  have h1 : x * d < y * d := mul_lt_mul_of_pos_right hxy hd
  have h2 : y * d < y * c := mul_lt_mul_of_pos_left hdc hy
  nlinarith

/-- `p_1 < p_2 < ...`: the exact thresholds increase strictly. -/
theorem staircaseP_lt_succ {m n s k : ℝ}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (hk : 1 ≤ k) (hks : k + 1 < s) :
    staircaseP m n s k < staircaseP m n s (k + 1) := by
  have hmpos : 0 < m := lt_of_lt_of_le (by norm_num) hm
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hkpos : 0 < k := lt_of_lt_of_le (by norm_num) hk
  have hk1pos : 0 < k + 1 := by linarith
  have hk1 : 1 ≤ k + 1 := by linarith
  have hks' : k < s := by linarith
  rw [staircaseP_eq_gamma_ratio hm hn hk hks',
    staircaseP_eq_gamma_ratio hm hn hk1 hks]
  have hkm : 1 < k * m := by
    have htwo : 2 ≤ k * m := by
      calc
        2 = 1 * 2 := by ring
        _ ≤ k * m := mul_le_mul hk hm (by norm_num) hkpos.le
    linarith
  have hkn : 1 < k * n := by
    have htwo : 2 ≤ k * n := by
      calc
        2 = 1 * 2 := by ring
        _ ≤ k * n := mul_le_mul hk hn (by norm_num) hkpos.le
    linarith
  have hγ : 0 < staircaseGamma m n k :=
    staircaseGamma_pos hm hn hk hks'
  have hden : 1 < k * (k + 1) * m * n := by
    have hkk : 2 ≤ k * (k + 1) := by
      calc
        2 = 1 * 2 := by ring
        _ ≤ k * (k + 1) := mul_le_mul hk (by linarith) (by norm_num) hkpos.le
    have hkkm : 4 ≤ k * (k + 1) * m := by
      calc
        4 = 2 * 2 := by ring
        _ ≤ (k * (k + 1)) * m :=
          mul_le_mul hkk hm (by norm_num) (by linarith)
    have hfull : 8 ≤ k * (k + 1) * m * n := by
      calc
        8 = 4 * 2 := by ring
        _ ≤ (k * (k + 1) * m) * n :=
          mul_le_mul hkkm hn (by norm_num) (by linarith)
    linarith
  have hfrac : 1 / (k * (k + 1) * m * n) < 1 := by
    rw [div_lt_iff₀ (lt_trans (by norm_num) hden)]
    linarith
  have hγinc :
      staircaseGamma m n k < staircaseGamma m n (k + 1) := by
    rw [← sub_pos, staircaseGamma_succ_sub (ne_of_gt hmpos) (ne_of_gt hnpos)
      (ne_of_gt hkpos) (ne_of_gt hk1pos)]
    linarith
  have hratio := ratio_lt_ratio_of_lt_of_gt (c := s - k) (d := s - (k + 1))
    hγ hγinc (by linarith) (by linarith)
  convert hratio using 1 <;> ring

end RankR
