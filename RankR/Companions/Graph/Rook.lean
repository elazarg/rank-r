/-
The rook-graph specialization of the graph-inclusion construction.

Vertices are pairs in `Fin q × Fin q`; two distinct vertices are adjacent when
they agree in exactly one coordinate.  The edge finset stores only the
increasing orientation.  A fixed row contains canonical cliques of every size
`R ≤ q`, which instantiate the exact threshold and all-level separation
theorems from `GraphSpectrahedron.lean`.
-/
import Mathlib.Data.Prod.Lex
import RankR.Companions.Graph.Dimensions
import RankR.Companions.Graph.Inclusion

namespace RankR

open Finset

section RookGraph

/-- Rook-graph vertices, equipped with the lexicographic order used to orient edges. -/
abbrev RookVertex (q : ℕ) :=
  Fin q ×ₗ Fin q

/-- Rook adjacency: equality in exactly one coordinate. -/
def rookAdjacent {q : ℕ} (x y : RookVertex q) : Prop :=
  ((ofLex x).1 = (ofLex y).1 ∧ (ofLex x).2 ≠ (ofLex y).2) ∨
    ((ofLex x).1 ≠ (ofLex y).1 ∧ (ofLex x).2 = (ofLex y).2)

instance rookAdjacentDecidable {q : ℕ} (x y : RookVertex q) :
    Decidable (rookAdjacent x y) := by
  unfold rookAdjacent
  infer_instance

/-- The increasingly oriented edge set of the `q × q` rook graph. -/
def rookEdges (q : ℕ) :
    Finset (RookVertex q × RookVertex q) :=
  Finset.univ.filter fun p =>
    p.1 < p.2 ∧ rookAdjacent p.1 p.2

theorem rookEdges_oriented {q : ℕ} :
    ∀ p ∈ rookEdges q, p.1 < p.2 := by
  intro p hp
  exact (Finset.mem_filter.mp hp).2.1

/-! ### Rook support and its cardinality -/

/-- The diagonal ordered pairs of rook vertices. -/
def rookDiagonalPairs (q : ℕ) :
    Finset (RookVertex q × RookVertex q) :=
  Finset.univ.filter fun p => p.1 = p.2

/-- The ordered adjacent pairs, i.e. the darts of the rook graph. -/
def rookAdjacentPairs (q : ℕ) :
    Finset (RookVertex q × RookVertex q) :=
  Finset.univ.filter fun p => rookAdjacent p.1 p.2

/-- Diagonal pairs are indexed by their common vertex. -/
def rookDiagonalPairsEquiv (q : ℕ) :
    rookDiagonalPairs q ≃ RookVertex q where
  toFun p := p.1.1
  invFun x := ⟨(x, x), by simp [rookDiagonalPairs]⟩
  left_inv p := by
    exact Subtype.ext (Prod.ext rfl (Finset.mem_filter.mp p.property).2)
  right_inv x := rfl

/-- Ordered distinct pairs from `Fin q`. -/
abbrev rookOffDiagonal (q : ℕ) :=
  (Finset.univ : Finset (Fin q)).offDiag

/-- Read a rook dart as either a fixed row with ordered distinct columns, or a
fixed column with ordered distinct rows. -/
def rookAdjacentPairCoordinates
    {q : ℕ} (p : rookAdjacentPairs q) :
    (Fin q × rookOffDiagonal q) ⊕ (rookOffDiagonal q × Fin q) :=
  if hrow : (ofLex p.1.1).1 = (ofLex p.1.2).1 then
    Sum.inl
      ((ofLex p.1.1).1,
        ⟨((ofLex p.1.1).2, (ofLex p.1.2).2), by
          rw [Finset.mem_offDiag]
          refine ⟨Finset.mem_univ _, Finset.mem_univ _, ?_⟩
          rcases (Finset.mem_filter.mp p.property).2 with h | h
          · exact h.2
          · exact (h.1 hrow).elim⟩)
  else
    Sum.inr
      (⟨((ofLex p.1.1).1, (ofLex p.1.2).1), by
          rw [Finset.mem_offDiag]
          exact ⟨Finset.mem_univ _, Finset.mem_univ _, hrow⟩⟩,
        (ofLex p.1.1).2)

/-- Build the corresponding rook dart from its row/column coordinates. -/
def rookCoordinatesAdjacentPair
    {q : ℕ}
    (z : (Fin q × rookOffDiagonal q) ⊕
      (rookOffDiagonal q × Fin q)) :
    rookAdjacentPairs q :=
  match z with
  | Sum.inl z =>
      ⟨(toLex (z.1, z.2.1.1), toLex (z.1, z.2.1.2)), by
        rw [rookAdjacentPairs, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, Or.inl ⟨rfl,
          (Finset.mem_offDiag.mp z.2.2).2.2⟩⟩⟩
  | Sum.inr z =>
      ⟨(toLex (z.1.1.1, z.2), toLex (z.1.1.2, z.2)), by
        rw [rookAdjacentPairs, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, Or.inr
          ⟨(Finset.mem_offDiag.mp z.1.2).2.2, rfl⟩⟩⟩

/-- A rook dart either fixes a row and chooses ordered distinct columns, or
fixes a column and chooses ordered distinct rows. -/
def rookAdjacentPairsEquivCoordinates (q : ℕ) :
    rookAdjacentPairs q ≃
      (Fin q × rookOffDiagonal q) ⊕ (rookOffDiagonal q × Fin q) where
  toFun := rookAdjacentPairCoordinates
  invFun := rookCoordinatesAdjacentPair
  left_inv p := by
    apply Subtype.ext
    unfold rookAdjacentPairCoordinates rookCoordinatesAdjacentPair
    split_ifs with hrow
    · change
        (p.1.1,
          toLex ((ofLex p.1.1).1, (ofLex p.1.2).2)) = p.1
      apply Prod.ext
      · rfl
      · exact ofLex.injective (Prod.ext hrow rfl)
    · have hcol :
          (ofLex p.1.1).2 = (ofLex p.1.2).2 := by
        rcases (Finset.mem_filter.mp p.property).2 with h | h
        · exact (hrow h.1).elim
        · exact h.2
      change
        (toLex ((ofLex p.1.1).1, (ofLex p.1.1).2),
          toLex ((ofLex p.1.2).1, (ofLex p.1.1).2)) = p.1
      apply Prod.ext
      · rfl
      · exact ofLex.injective (Prod.ext rfl hcol)
  right_inv z := by
    rcases z with z | z
    · simp [rookAdjacentPairCoordinates, rookCoordinatesAdjacentPair]
    · have hne := (Finset.mem_offDiag.mp z.1.2).2.2
      simp [rookAdjacentPairCoordinates, rookCoordinatesAdjacentPair, hne]

@[simp] theorem card_rookDiagonalPairs (q : ℕ) :
    (rookDiagonalPairs q).card = q * q := by
  rw [← Fintype.card_coe,
    Fintype.card_congr (rookDiagonalPairsEquiv q)]
  simp only [RookVertex, Fintype.card_lex, Fintype.card_prod,
    Fintype.card_fin]

@[simp] theorem card_rookAdjacentPairs (q : ℕ) :
    (rookAdjacentPairs q).card = q * q * (2 * (q - 1)) := by
  rw [← Fintype.card_coe,
    Fintype.card_congr (rookAdjacentPairsEquivCoordinates q)]
  simp only [Fintype.card_sum, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_coe, Finset.offDiag_card,
    Finset.card_univ]
  have hoff : q * q - q = q * (q - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one]
  rw [hoff]
  ring

theorem disjoint_rookDiagonalPairs_rookAdjacentPairs (q : ℕ) :
    Disjoint (rookDiagonalPairs q) (rookAdjacentPairs q) := by
  rw [Finset.disjoint_left]
  intro p hdiag hadj
  have hpp : p.1 = p.2 := (Finset.mem_filter.mp hdiag).2
  have ha : rookAdjacent p.1 p.2 := (Finset.mem_filter.mp hadj).2
  simp [hpp, rookAdjacent] at ha

/-- For the rook edge set, the graph matrix support is exactly the disjoint
union of the diagonal and all ordered adjacent pairs. -/
theorem graphMatrixSupport_rookEdges (q : ℕ) :
    graphMatrixSupport (rookEdges q)
      = rookDiagonalPairs q ∪ rookAdjacentPairs q := by
  ext p
  simp only [mem_graphMatrixSupport, Finset.mem_union,
    rookDiagonalPairs, rookAdjacentPairs, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro (hdiag | hedge | hedge)
    · exact Or.inl hdiag
    · exact Or.inr (Finset.mem_filter.mp hedge).2.2
    · exact Or.inr <| by
        rcases (Finset.mem_filter.mp hedge).2.2 with
          (hrow | hcol)
        · exact Or.inl ⟨hrow.1.symm, Ne.symm hrow.2⟩
        · exact Or.inr ⟨Ne.symm hcol.1, hcol.2.symm⟩
  · rintro (hdiag | hadj)
    · exact Or.inl hdiag
    · have hne : p.1 ≠ p.2 := by
        intro hp
        simp [hp, rookAdjacent] at hadj
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inr <| Or.inl <| by
          rw [rookEdges, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hlt, hadj⟩
      · exact Or.inr <| Or.inr <| by
          rw [rookEdges, Finset.mem_filter]
          refine ⟨Finset.mem_univ _, hgt, ?_⟩
          rcases hadj with hrow | hcol
          · exact Or.inl ⟨hrow.1.symm, Ne.symm hrow.2⟩
          · exact Or.inr ⟨Ne.symm hcol.1, hcol.2.symm⟩

/-- The rook graph operator system has complex dimension
`q²(2q-1)`. -/
theorem card_graphMatrixSupport_rookEdges (q : ℕ) :
    (graphMatrixSupport (rookEdges q)).card
      = q * q * (2 * q - 1) := by
  rw [graphMatrixSupport_rookEdges,
    Finset.card_union_of_disjoint
      (disjoint_rookDiagonalPairs_rookAdjacentPairs q)]
  simp only [card_rookDiagonalPairs, card_rookAdjacentPairs]
  cases q with
  | zero => norm_num
  | succ q =>
      simp only [Nat.succ_sub_one]
      have hsub : 2 * (q + 1) - 1 = 2 * q + 1 := by omega
      rw [hsub]
      ring

/-- The exact complex dimension of the rook graph operator system. -/
theorem finrank_rookGraphOperatorSpace (q : ℕ) :
    Module.finrank ℂ (graphOperatorSpace (rookEdges q))
      = q * q * (2 * q - 1) := by
  rw [finrank_graphOperatorSpace,
    card_graphMatrixSupport_rookEdges]

/-- The exact complex dimension of the protected two-layer coefficient
system. -/
theorem finrank_rookGraphTwoLayerSpace (q : ℕ) :
    Module.finrank ℂ (graphTwoLayerSpace (rookEdges q))
      = 2 * q * q * (2 * q - 1) := by
  rw [finrank_graphTwoLayerSpace,
    finrank_rookGraphOperatorSpace]
  ring

/-- Removing the identity coordinate from the two-layer dimension gives the
displayed protected coefficient count. -/
theorem rookGraphTwoLayerDimension_sub_one (q : ℕ) :
    Module.finrank ℂ (graphTwoLayerSpace (rookEdges q)) - 1
      = 2 * q * q * (2 * q - 1) - 1 := by
  rw [finrank_rookGraphTwoLayerSpace]

/-- The full matrix dictionary on `M_{2q²}` has complex dimension `4q⁴`. -/
theorem finrank_rookAmbientMatrix (q : ℕ) :
    Module.finrank ℂ
        (Matrix (RookVertex q × Fin 2) (RookVertex q × Fin 2) ℂ)
      = 4 * q ^ 4 := by
  rw [Module.finrank_matrix]
  simp only [Fintype.card_prod, Fintype.card_lex, Fintype.card_fin,
    Module.finrank_self, mul_one]
  ring

/-- Removing the identity coordinate from the full matrix dimension gives the
tomographically complete comparison count in the rook corollary. -/
theorem rookAmbientDimension_sub_one (q : ℕ) :
    Module.finrank ℂ
        (Matrix (RookVertex q × Fin 2) (RookVertex q × Fin 2) ℂ) - 1
      = 4 * q ^ 4 - 1 := by
  rw [finrank_rookAmbientMatrix]

/-- Embed `Fin R` as the first `R` vertices of a fixed rook-graph row. -/
def rookRowEmbedding
    {q R : ℕ} (row : Fin q) (hRq : R ≤ q) :
    Fin R ↪ RookVertex q where
  toFun j := toLex (row, Fin.castLE hRq j)
  inj' := by
    intro i j hij
    exact Fin.ext (congrArg (fun p => (ofLex p).2.val) hij)

/-- The canonical `R`-clique inside a fixed row. -/
def rookRowClique
    {q R : ℕ} (row : Fin q) (hRq : R ≤ q) :
    Finset (RookVertex q) :=
  Finset.univ.map (rookRowEmbedding row hRq)

@[simp] theorem card_rookRowClique
    {q R : ℕ} (row : Fin q) (hRq : R ≤ q) :
    (rookRowClique row hRq).card = R := by
  simp [rookRowClique]

theorem mem_rookEdges_of_same_row
    {q : ℕ} {x y : RookVertex q}
    (hxy : x < y) (hrow : (ofLex x).1 = (ofLex y).1) :
    (x, y) ∈ rookEdges q := by
  rw [rookEdges, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, hxy, Or.inl ⟨hrow, ?_⟩⟩
  intro hcol
  exact (ne_of_lt hxy) (ofLex.injective (Prod.ext hrow hcol))

/-- Every canonical row set is a clique in the oriented rook edge set. -/
theorem rookRowClique_isClique
    {q R : ℕ} (row : Fin q) (hRq : R ≤ q) :
    ∀ i ∈ rookRowClique row hRq,
      ∀ j ∈ rookRowClique row hRq,
        i < j → (i, j) ∈ rookEdges q := by
  intro i hi j hj hij
  rw [rookRowClique, Finset.mem_map] at hi hj
  obtain ⟨a, -, rfl⟩ := hi
  obtain ⟨b, -, rfl⟩ := hj
  exact mem_rookEdges_of_same_row hij rfl

/-- The rook graph has the exact protected threshold `R-1` at every
`1 ≤ R ≤ q`, in the canonical `Fin R` level coordinates. -/
theorem rookGraphLevelInclusion_iff
    {q R : ℕ} (hR : 0 < R) (hRq : R ≤ q)
    (row : Fin q) (lam : ℝ) :
    GraphLevelInclusion
        (U := RookVertex q) (L := Fin R)
        (rookEdges q) R lam
      ↔ (R : ℝ) - 1 ≤ lam := by
  let S := rookRowClique row hRq
  have hS : S.card = R := card_rookRowClique row hRq
  have hcl :
      ∀ i ∈ S, ∀ j ∈ S, i < j →
        (i, j) ∈ rookEdges q :=
    rookRowClique_isClique row hRq
  let e : S ≃ Fin R :=
    Fintype.equivOfCardEq (by simp [hS])
  have hlevel :
      GraphLevelInclusion
          (U := RookVertex q) (L := Fin R)
          (rookEdges q) R lam
        ↔
      GraphLevelInclusion
          (U := RookVertex q) (L := S)
          (rookEdges q) R lam := by
    constructor
    · intro h
      exact graphLevelInclusion_of_embedding e.toEmbedding h
    · intro h
      exact graphLevelInclusion_of_embedding e.symm.toEmbedding h
  rw [hlevel]
  exact graphCliqueLevelInclusion_iff
    rookEdges_oriented hR hS hcl lam

/-- For `R < q`, the rook graph separates all matrix levels exactly at `R`. -/
theorem rookGraphProtectedLevelInclusion_iff
    {q R : ℕ} (hR : 0 < R) (hRq : R < q)
    (row : Fin q) (n : ℕ) :
    GraphLevelInclusion
        (U := RookVertex q) (L := Fin n)
        (rookEdges q) R ((R : ℝ) - 1)
      ↔ n ≤ R := by
  let S := rookRowClique row (Nat.succ_le_iff.mpr hRq)
  have hS : S.card = R + 1 :=
    card_rookRowClique row (Nat.succ_le_iff.mpr hRq)
  exact graphProtectedLevelInclusion_iff
    rookEdges_oriented hR hS
      (rookRowClique_isClique row (Nat.succ_le_iff.mpr hRq)) n

end RookGraph

end RankR
