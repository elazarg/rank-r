/-
The rank-sensitive partial-trace inequality after subtracting a scalar
multiple of the trace term.
-/
import RankR.Core.PartialTrace.Main
import RankR.Library.Matrix.Rank

namespace RankR

open Matrix

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]

/-- A centered form of the rank-sensitive partial-trace bound. -/
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

end RankR
