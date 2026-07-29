/-
Ky Fan at `k = 2`, as a statement about weights.

The action of an operator on an orthonormal pair, expanded over a spectral
decomposition, is `∑ᵢ cᵢ θᵢ` with `θᵢ = ‖P wᵢ‖² ∈ [0,1]` and `∑ᵢ θᵢ = Tr P = 2`.
Such a sum is bounded by the two largest `cᵢ`.  Stated existentially: some pair
of distinct indices dominates.  That is all the caller needs, because the bound
it feeds this into holds for *every* pair of distinct indices, so no ordering of
the `cᵢ` has to be produced.
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace RankR

open Finset

/-- **Ky Fan at `k = 2`, in weight form.**  If the weights `θᵢ` lie in `[0,1]`
and sum to `2`, then `∑ᵢ cᵢ θᵢ` is at most `c a + c b` for some pair of distinct
indices `a ≠ b`.  No sign condition on `c` is needed.

Take `a` maximizing `c` and `b` maximizing `c` off `a`.  Every other index has
`cᵢ ≤ c b`, so bounding the tail by `c b` and using `∑ θ = 2` gives
`∑ᵢ cᵢθᵢ ≤ c a · θ a + c b · (2 − θ a) = 2 c b + θ a (c a − c b) ≤ c a + c b`,
the last step by `θ a ≤ 1` and `c b ≤ c a`. -/
theorem exists_pair_sum_weighted_le {ι : Type*} [Fintype ι] (c θ : ι → ℝ)
    (h0 : ∀ i, 0 ≤ θ i) (h1 : ∀ i, θ i ≤ 1)
    (hsum : ∑ i, θ i = 2) :
    ∃ a b : ι, a ≠ b ∧ ∑ i, c i * θ i ≤ c a + c b := by
  classical
  -- `ι` has at least two elements, since `2 = ∑ᵢ θᵢ ≤ ∑ᵢ 1 = card ι`.
  have hcard : 2 ≤ Fintype.card ι := by
    have h : ∑ i, θ i ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum fun i _ => h1 i
    rw [hsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
    exact_mod_cast h
  have huniv : (Finset.univ : Finset ι).Nonempty := by
    rw [← Finset.card_pos, Finset.card_univ]; omega
  -- `a` maximizes `c`, and `b` maximizes `c` away from `a`.
  obtain ⟨a, -, ha⟩ := Finset.exists_max_image (Finset.univ : Finset ι) c huniv
  have herase : (Finset.univ.erase a : Finset ι).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ]
    omega
  obtain ⟨b, hbmem, hb⟩ := Finset.exists_max_image (Finset.univ.erase a) c herase
  refine ⟨a, b, Ne.symm (Finset.ne_of_mem_erase hbmem), ?_⟩
  -- Peel `a` and `b` off any sum over `univ`.
  have key : ∀ f : ι → ℝ,
      ∑ i, f i = f a + f b + ∑ i ∈ (Finset.univ.erase a).erase b, f i := by
    intro f
    rw [← Finset.add_sum_erase _ f (Finset.mem_univ a), ← Finset.add_sum_erase _ f hbmem]
    ring
  have hba : c b ≤ c a := ha b (Finset.mem_univ b)
  have htail : ∑ i ∈ (Finset.univ.erase a).erase b, c i * θ i
      ≤ c b * ∑ i ∈ (Finset.univ.erase a).erase b, θ i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_right (hb i (Finset.mem_of_mem_erase hi)) (h0 i)
  have hrest : θ b + ∑ i ∈ (Finset.univ.erase a).erase b, θ i = 2 - θ a := by
    have h := key θ
    rw [hsum] at h
    linarith
  calc ∑ i, c i * θ i
      = c a * θ a + c b * θ b + ∑ i ∈ (Finset.univ.erase a).erase b, c i * θ i :=
        key fun i => c i * θ i
    _ ≤ c a * θ a + c b * θ b + c b * ∑ i ∈ (Finset.univ.erase a).erase b, θ i := by linarith
    _ = c a * θ a + c b * (2 - θ a) := by rw [← hrest]; ring
    _ ≤ c a + c b := by
        linarith [mul_le_mul_of_nonneg_right (h1 a) (sub_nonneg.mpr hba)]

end RankR
