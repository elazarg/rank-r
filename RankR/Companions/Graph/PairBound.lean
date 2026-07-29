/-
The exact pair-amplification threshold for a graph family with a clique.
-/
import RankR.Core.Amplification.Pair
import RankR.Companions.Graph.Threshold

namespace RankR

open Matrix Finset ComplexConjugate

section Clique

variable {U : Type*} [Fintype U] [DecidableEq U] [LinearOrder U]

/-- **The amplification threshold of a graph family is `R - 1`** (`thm:clique`).

For a graph with an `R`-clique, `Θ^{Φ_G}_{R,λ}` is `R`-positive exactly for
`λ ≥ R - 1`.  The upper half is pair amplification with `β₂(Φ_G) = 1`
(`choiTwoBound_graphKraus`, `thetaPositive_of_choiTwoBound`); the lower half is
the clique witness (`sub_one_le_lam_of_clique`). -/
theorem thetaPositive_graphKraus_iff
    {E : Finset (U × U)} (hE : ∀ p ∈ E, p.1 < p.2)
    {R : ℕ} (hR : 0 < R) {S : Finset U} (hSR : S.card = R)
    (hcl : ∀ i ∈ S, ∀ j ∈ S, i < j → (i, j) ∈ E) (lam : ℝ) :
    ThetaPositive (graphKraus E) R lam ↔ (R : ℝ) - 1 ≤ lam := by
  refine ⟨fun h => sub_one_le_lam_of_clique hE hR h hSR hcl, fun h => ?_⟩
  refine thetaPositive_mono hR ?_ h
  have := thetaPositive_of_choiTwoBound (A := graphKraus E) (β := 1)
    zero_le_one (choiTwoBound_graphKraus hE) (graphKraus_transpose E) R
  simpa using this

end Clique

end RankR
