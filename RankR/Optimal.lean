/-
Optimality of the coefficients `r` and `1/r` of `thm:rank_r`.

The extremizer `C = P_r ⊗ |v⟩⟨w|` is realized as `projWit S x₀ x₁`, with `P_r`
the diagonal projection onto a set `S` of `r` coordinates of `U` and `v, w` two
standard basis vectors `δ_{x₀}, δ_{x₁}` of `V`.  Both test cases of the
sharpness discussion are this one matrix: `v ⊥ w` is `x₀ ≠ x₁`, and `v = w` is
`x₀ = x₁`.  Its four quantities are

  ‖C‖₂² = r,   |Tr C|² = r²|⟨w, v⟩|²,   ‖Tr_U C‖₂² = r²,   ‖Tr_V C‖₂² = r|⟨w, v⟩|²,

so it attains equality in `eq:main-bound`, and the two test cases force `a ≥ r`
and then `b ≥ 1/r` for any bound `‖Tr_U C‖₂² + ‖Tr_V C‖₂² ≤ a‖C‖₂² + b|Tr C|²`
valid at rank `r`.  Nothing here is conditional on the Fu-Gao-Park estimate.
-/
import RankR.HS
import Mathlib.LinearAlgebra.Matrix.Rank

namespace RankR

open Matrix Finset ComplexConjugate

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]

section Witness

variable (S : Finset U) (x₀ x₁ : V)

/-- The column factor of the extremizer: `∑_{u ∈ S} |u ⊗ δ_{x₀}⟩⟨u|`. -/
def projWitCol : Matrix (U × V) {u // u ∈ S} ℂ :=
  Matrix.of fun p i => (if p.1 = i.1 then 1 else 0) * (if p.2 = x₀ then 1 else 0)

/-- The row factor of the extremizer: `∑_{u ∈ S} |u⟩⟨u ⊗ δ_{x₁}|`. -/
def projWitRow : Matrix {u // u ∈ S} (U × V) ℂ :=
  Matrix.of fun i q => (if q.1 = i.1 then 1 else 0) * (if q.2 = x₁ then 1 else 0)

/-- **The extremizer for `thm:rank_r`**, `P_S ⊗ |δ_{x₀}⟩⟨δ_{x₁}|`. -/
def projWit : Matrix (U × V) (U × V) ℂ :=
  Matrix.of fun p q =>
    (if p.1 = q.1 ∧ p.1 ∈ S then 1 else 0) *
      ((if p.2 = x₀ then 1 else 0) * (if q.2 = x₁ then 1 else 0))

omit [Fintype U] [Fintype V] in
@[simp]
theorem projWit_apply (p q : U × V) :
    projWit S x₀ x₁ p q =
      (if p.1 = q.1 ∧ p.1 ∈ S then 1 else 0) *
        ((if p.2 = x₀ then 1 else 0) * (if q.2 = x₁ then 1 else 0)) := rfl

omit [Fintype U] [Fintype V] in
/-- The extremizer factors through `S`, which is what bounds its rank. -/
theorem projWit_eq_mul : projWit S x₀ x₁ = projWitCol S x₀ * projWitRow S x₁ := by
  ext p q
  rw [projWit_apply, Matrix.mul_apply]
  simp only [projWitCol, projWitRow, Matrix.of_apply]
  rw [Finset.sum_coe_sort S fun u =>
    ((if p.1 = u then (1 : ℂ) else 0) * (if p.2 = x₀ then 1 else 0)) *
      ((if q.1 = u then 1 else 0) * (if q.2 = x₁ then 1 else 0))]
  simp only [mul_ite, mul_one, mul_zero]
  by_cases hq : q.1 = p.1 <;> by_cases hS : p.1 ∈ S <;>
    simp_all [eq_comm, and_comm]

/-- The extremizer has rank at most `S.card`, since it factors through `S`. -/
theorem rank_projWit_le : (projWit S x₀ x₁).rank ≤ S.card := by
  rw [projWit_eq_mul]
  refine (Matrix.rank_mul_le_left _ _).trans ?_
  simpa using Matrix.rank_le_card_width (projWitCol S x₀)

/-- The two factors compose to the identity on `S` in the other order. -/
theorem projWitRow_mul_projWitCol (x : V) :
    projWitRow S x * projWitCol S x = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [projWitCol, projWitRow, Matrix.of_apply, Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_ite, mul_one, mul_zero,
    Subtype.ext_iff, @eq_comm _ (j : U) (i : U)]

/-- **The extremizer has rank exactly `r`.**  Sandwiching it between the two
factors of the opposite pair returns the identity on `S`, so its rank is at
least `S.card`; `rank_projWit_le` is the reverse. -/
theorem rank_projWit : (projWit S x₀ x₁).rank = S.card := by
  refine le_antisymm (rank_projWit_le S x₀ x₁) ?_
  have hsandwich : projWitRow S x₀ * projWit S x₀ x₁ * projWitCol S x₁ = 1 := by
    rw [projWit_eq_mul, ← Matrix.mul_assoc (projWitRow S x₀),
      projWitRow_mul_projWitCol, Matrix.one_mul, projWitRow_mul_projWitCol]
  have hle := (Matrix.rank_mul_le_left (projWitRow S x₀ * projWit S x₀ x₁)
    (projWitCol S x₁)).trans (Matrix.rank_mul_le_right (projWitRow S x₀) (projWit S x₀ x₁))
  rw [hsandwich, Matrix.rank_one] at hle
  simpa using hle

/-- `‖C‖₂² = r` for the extremizer. -/
theorem hsNormSq_projWit : hsNormSq (projWit S x₀ x₁) = S.card := by
  simp [hsNormSq, Fintype.sum_prod_type, apply_ite Complex.normSq, ite_and,
    Finset.sum_ite_eq, Finset.sum_ite_eq']

/-- `Tr C = r⟨w, v⟩` for the extremizer; the inner product is `1` when the two
basis vectors coincide and `0` otherwise. -/
theorem trace_projWit :
    (projWit S x₀ x₁).trace = if x₀ = x₁ then (S.card : ℂ) else 0 := by
  simp [Matrix.trace, Matrix.diag_apply, Fintype.sum_prod_type,
    Finset.sum_ite_eq', @eq_comm _ x₁ x₀]

/-- `Tr_U C = r|δ_{x₀}⟩⟨δ_{x₁}|`, so `‖Tr_U C‖₂² = r²`. -/
theorem hsNormSq_ptraceU_projWit :
    hsNormSq (ptraceU (projWit S x₀ x₁)) = (S.card : ℝ) ^ 2 := by
  have h : ∀ b c : V, ptraceU (projWit S x₀ x₁) b c
      = (S.card : ℂ) * ((if b = x₀ then 1 else 0) * (if c = x₁ then 1 else 0)) := by
    intro b c
    simp
  simp [hsNormSq, h, apply_ite Complex.normSq, Finset.sum_ite_eq',
    Complex.normSq_natCast]
  ring

/-- `Tr_V C = ⟨w, v⟩ P_S`, so `‖Tr_V C‖₂² = r|⟨w, v⟩|²`. -/
theorem hsNormSq_ptraceV_projWit :
    hsNormSq (ptraceV (projWit S x₀ x₁)) = if x₀ = x₁ then (S.card : ℝ) else 0 := by
  have h : ∀ u u' : U, ptraceV (projWit S x₀ x₁) u u'
      = (if u = u' ∧ u ∈ S then 1 else 0) * (if x₀ = x₁ then 1 else 0) := by
    intro u u'
    simp [Finset.sum_ite_eq', @eq_comm _ x₁ x₀]
  simp [hsNormSq, h, apply_ite Complex.normSq, ite_and, Finset.sum_ite_eq]

/-- **The extremizer attains `eq:main-bound` at `r = S.card`**, so the pair of
coefficients `(r, 1/r)` is achieved and not merely approached: with `‖C‖₂² = r`,
`|Tr C|² = r²|⟨w, v⟩|²`, both sides equal `r² + r|⟨w, v⟩|²`. -/
theorem projWit_bound_eq {r : ℕ} (hr : 0 < r) (hS : S.card = r) :
    hsNormSq (ptraceU (projWit S x₀ x₁)) + hsNormSq (ptraceV (projWit S x₀ x₁))
      = r * hsNormSq (projWit S x₀ x₁)
        + (1 / r : ℝ) * Complex.normSq (projWit S x₀ x₁).trace := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  rw [hsNormSq_ptraceU_projWit, hsNormSq_ptraceV_projWit, hsNormSq_projWit,
    trace_projWit, hS]
  split_ifs with h
  · rw [Complex.normSq_natCast]
    field_simp
  · simp [sq]

end Witness

section Optimality

variable {r : ℕ}

/-- **The coefficient `r` of `‖C‖₂²` is optimal.**  Testing a bound with
coefficients `a, b` on the extremizer with `x₀ ≠ x₁` kills the trace term and
leaves `r² ≤ a·r`, so `a ≥ r` whatever `b` is. -/
theorem le_coeff_hsNormSq_of_bound (hr : 0 < r) (hU : r ≤ Fintype.card U)
    (hV : 2 ≤ Fintype.card V) {a b : ℝ}
    (h : ∀ C : Matrix (U × V) (U × V) ℂ, C.rank ≤ r →
      hsNormSq (ptraceU C) + hsNormSq (ptraceV C)
        ≤ a * hsNormSq C + b * Complex.normSq C.trace) :
    (r : ℝ) ≤ a := by
  obtain ⟨S, -, hcard⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset U))
    (by simpa using hU)
  obtain ⟨x₀, x₁, hx⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card V)
  have hkey := h (projWit S x₀ x₁) (by simpa [hcard] using (rank_projWit S x₀ x₁).le)
  rw [hsNormSq_ptraceU_projWit, hsNormSq_ptraceV_projWit, hsNormSq_projWit,
    trace_projWit, if_neg hx, if_neg hx, hcard] at hkey
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  simp only [Complex.normSq_zero, mul_zero, add_zero] at hkey
  nlinarith

/-- **Once `a = r` is fixed, the coefficient `1/r` of `|Tr C|²` is optimal.**
Testing on the same extremizer with `x₀ = x₁` leaves `r² + r ≤ r² + b·r²`. -/
theorem inv_le_coeff_trace_of_bound (hr : 0 < r) (hU : r ≤ Fintype.card U)
    (hV : 0 < Fintype.card V) {b : ℝ}
    (h : ∀ C : Matrix (U × V) (U × V) ℂ, C.rank ≤ r →
      hsNormSq (ptraceU C) + hsNormSq (ptraceV C)
        ≤ (r : ℝ) * hsNormSq C + b * Complex.normSq C.trace) :
    1 / (r : ℝ) ≤ b := by
  obtain ⟨S, -, hcard⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset U))
    (by simpa using hU)
  obtain ⟨x₀⟩ := Fintype.card_pos_iff.mp hV
  have hkey := h (projWit S x₀ x₀) (by simpa [hcard] using (rank_projWit S x₀ x₀).le)
  rw [hsNormSq_ptraceU_projWit, hsNormSq_ptraceV_projWit, hsNormSq_projWit,
    trace_projWit, if_pos rfl, if_pos rfl, hcard] at hkey
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  rw [Complex.normSq_natCast] at hkey
  rw [div_le_iff₀ hrpos]
  nlinarith

end Optimality

end RankR
