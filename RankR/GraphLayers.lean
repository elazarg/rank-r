/-
The two-layer compression of the graph Kraus family.

For an edge set `E` on `U`, the manuscript's graph reduction is

  `R_G(X) = ∑ₑ Lₑ Xᵀ Lₑᴴ`,

where `Lₑ = Eᵢⱼ - Eⱼᵢ`.  The graph Kraus operator is
`Aₑ = Lₑ ⊗ J`, with `J = E₀₁ - E₁₀`.  Keeping the two diagonal qubit
layers gives the exact action

  `(Φ_G ∘ τ)(X ⊗ p + Y ⊗ q)
      = R_G(Y) ⊗ p + R_G(X) ⊗ q`.

This file proves that coordinate identity.  The operator-system and
free-spectrahedral vocabulary built on top of it is kept separate.
-/
import RankR.ThetaBound
import RankR.MapPos
import Mathlib.Analysis.Matrix.Order

namespace RankR

open Matrix Finset ComplexConjugate
open scoped ComplexOrder Kronecker MatrixOrder

section QubitLayers

/-- The `|0⟩⟨0|` qubit layer. -/
def qubitP : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.single 0 0 1

/-- The `|1⟩⟨1|` qubit layer. -/
def qubitQ : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.single 1 1 1

/-- The real skew qubit generator is skew-adjoint. -/
theorem skewUnit_qubit_conjTranspose :
    (skewUnit (0 : Fin 2) 1)ᴴ = -skewUnit 0 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [skewUnit, Matrix.conjTranspose_apply, Matrix.single_apply]

/-- The skew qubit generator exchanges the two diagonal layers. -/
theorem skewUnit_qubit_conj_qubitP :
    skewUnit (0 : Fin 2) 1 * qubitP * (skewUnit 0 1)ᴴ = qubitQ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [skewUnit, qubitP, qubitQ, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.single_apply]

/-- The skew qubit generator exchanges the two diagonal layers. -/
theorem skewUnit_qubit_conj_qubitQ :
    skewUnit (0 : Fin 2) 1 * qubitQ * (skewUnit 0 1)ᴴ = qubitP := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [skewUnit, qubitP, qubitQ, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.single_apply]

@[simp] theorem qubitP_transpose : qubitPᵀ = qubitP := by
  simp [qubitP]

@[simp] theorem qubitQ_transpose : qubitQᵀ = qubitQ := by
  simp [qubitQ]

end QubitLayers

section GraphReduction

variable {U : Type*} [Fintype U] [DecidableEq U] [LinearOrder U]

/-- The graph reduction map `R_G(X) = ∑ₑ Lₑ Xᵀ Lₑᴴ`. -/
noncomputable def graphReduction (E : Finset (U × U)) (X : Matrix U U ℂ) :
    Matrix U U ℂ :=
  ∑ e : {p : U × U // p ∈ E},
    skewUnit e.val.1 e.val.2 * Xᵀ * (skewUnit e.val.1 e.val.2)ᴴ

/-- The transposed graph Kraus map `Φ_G ∘ τ`. -/
noncomputable def graphPhiTranspose
    (E : Finset (U × U))
    (Z : Matrix (U × Fin 2) (U × Fin 2) ℂ) :
    Matrix (U × Fin 2) (U × Fin 2) ℂ :=
  krausSum (graphKraus E) Zᵀ

omit [LinearOrder U] in
/-- One graph Kraus term sends the lower diagonal layer to the upper one. -/
theorem edgeKraus_conj_layerP
    (e : U × U) (X : Matrix U U ℂ) :
    edgeKraus e * (X ⊗ₖ qubitP)ᵀ * (edgeKraus e)ᴴ
      =
    (skewUnit e.1 e.2 * Xᵀ * (skewUnit e.1 e.2)ᴴ) ⊗ₖ qubitQ := by
  rw [edgeKraus, ← Matrix.kroneckerMap_transpose,
    Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, qubitP_transpose,
    skewUnit_qubit_conj_qubitP]

omit [LinearOrder U] in
/-- One graph Kraus term sends the upper diagonal layer to the lower one. -/
theorem edgeKraus_conj_layerQ
    (e : U × U) (X : Matrix U U ℂ) :
    edgeKraus e * (X ⊗ₖ qubitQ)ᵀ * (edgeKraus e)ᴴ
      =
    (skewUnit e.1 e.2 * Xᵀ * (skewUnit e.1 e.2)ᴴ) ⊗ₖ qubitP := by
  rw [edgeKraus, ← Matrix.kroneckerMap_transpose,
    Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, qubitQ_transpose,
    skewUnit_qubit_conj_qubitQ]

omit [LinearOrder U] in
/-- **The two-layer action** (`eq:layer` for `Φ_G ∘ τ`).

The graph reduction is applied to the opposite layer. -/
theorem graphPhiTranspose_layers
    (E : Finset (U × U)) (X Y : Matrix U U ℂ) :
    graphPhiTranspose E (X ⊗ₖ qubitP + Y ⊗ₖ qubitQ)
      = graphReduction E Y ⊗ₖ qubitP
          + graphReduction E X ⊗ₖ qubitQ := by
  rw [graphPhiTranspose, krausSum, Matrix.transpose_add]
  simp_rw [graphKraus, Matrix.mul_add, Matrix.add_mul,
    edgeKraus_conj_layerP, edgeKraus_conj_layerQ]
  rw [Finset.sum_add_distrib]
  ext p q
  simp [graphReduction, Matrix.kroneckerMap_apply,
    Matrix.sum_apply, Finset.sum_mul]
  ring

end GraphReduction

section CorrectedLayers

variable {U : Type*} [Fintype U] [DecidableEq U] [LinearOrder U]

/-- The corrected graph map
`Θ^G_{R,λ} = Φ_G ∘ τ + λ (Δ - id/R)`, as an actual coordinate map. -/
noncomputable def graphTheta
    (E : Finset (U × U)) (R : ℕ) (lam : ℂ)
    (Z : Matrix (U × Fin 2) (U × Fin 2) ℂ) :
    Matrix (U × Fin 2) (U × Fin 2) ℂ :=
  graphPhiTranspose E Z
    + lam • (Z.trace • (1 : Matrix (U × Fin 2) (U × Fin 2) ℂ)
      - (R : ℂ)⁻¹ • Z)

omit [DecidableEq U] [LinearOrder U] in
/-- The trace of a two-layer matrix is the sum of its layer traces. -/
theorem trace_layers (X Y : Matrix U U ℂ) :
    (X ⊗ₖ qubitP + Y ⊗ₖ qubitQ).trace = X.trace + Y.trace := by
  rw [Matrix.trace_add, Matrix.trace_kronecker, Matrix.trace_kronecker]
  norm_num [qubitP, qubitQ, Matrix.trace]

omit [LinearOrder U] in
/-- The two diagonal qubit layers sum to the qubit identity. -/
theorem qubitP_add_qubitQ : qubitP + qubitQ = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [qubitP, qubitQ, Matrix.single_apply, Matrix.one_apply]

omit [LinearOrder U] in
/-- **The full two-layer action** (`eq:layer`).

The Kraus term exchanges layers, while the discard term depends on the sum of
the two traces and the protected identity term stays in its original layer. -/
theorem graphTheta_layers
    (E : Finset (U × U)) (R : ℕ) (lam : ℂ)
    (X Y : Matrix U U ℂ) :
    graphTheta E R lam (X ⊗ₖ qubitP + Y ⊗ₖ qubitQ)
      =
      (graphReduction E Y
          + lam • ((X.trace + Y.trace) • (1 : Matrix U U ℂ)
            - (R : ℂ)⁻¹ • X)) ⊗ₖ qubitP
        +
      (graphReduction E X
          + lam • ((X.trace + Y.trace) • (1 : Matrix U U ℂ)
            - (R : ℂ)⁻¹ • Y)) ⊗ₖ qubitQ := by
  rw [graphTheta, graphPhiTranspose_layers, trace_layers]
  ext p q
  obtain ⟨i, a⟩ := p
  obtain ⟨j, b⟩ := q
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.kroneckerMap_apply, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply, qubitP, qubitQ,
      Prod.ext_iff]

end CorrectedLayers

/-! ## The invariant coefficient spaces -/

section OperatorSpaces

variable {U : Type*} [Fintype U] [DecidableEq U] [LinearOrder U]

/-- Matrices supported on the diagonal and the two orientations of the edges
in `E`.  This is the coordinate graph operator system `S_G`. -/
def graphOperatorSpace (E : Finset (U × U)) :
    Submodule ℂ (Matrix U U ℂ) where
  carrier :=
    {X | ∀ i j, ¬(i = j ∨ (i, j) ∈ E ∨ (j, i) ∈ E) → X i j = 0}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY i j hij
    simp [hX i j hij, hY i j hij]
  smul_mem' := by
    intro c X hX i j hij
    simp [hX i j hij]

omit [Fintype U] [DecidableEq U] [LinearOrder U] in
theorem mem_graphOperatorSpace_iff
    {E : Finset (U × U)} {X : Matrix U U ℂ} :
    X ∈ graphOperatorSpace E
      ↔ ∀ i j, ¬(i = j ∨ (i, j) ∈ E ∨ (j, i) ∈ E) → X i j = 0 :=
  Iff.rfl

omit [Fintype U] [LinearOrder U] in
/-- The graph coefficient space contains the identity. -/
theorem one_mem_graphOperatorSpace (E : Finset (U × U)) :
    (1 : Matrix U U ℂ) ∈ graphOperatorSpace E := by
  intro i j h
  rw [Matrix.one_apply, if_neg]
  exact fun hij => h (Or.inl hij)

omit [Fintype U] [DecidableEq U] [LinearOrder U] in
/-- The graph coefficient space is closed under conjugate transpose. -/
theorem conjTranspose_mem_graphOperatorSpace
    {E : Finset (U × U)} {X : Matrix U U ℂ}
    (hX : X ∈ graphOperatorSpace E) :
    Xᴴ ∈ graphOperatorSpace E := by
  intro i j h
  rw [Matrix.conjTranspose_apply, RCLike.star_def,
    hX j i]
  · simp
  · intro hji
    rcases hji with hji | hji | hji
    · exact h (Or.inl hji.symm)
    · exact h (Or.inr (Or.inr hji))
    · exact h (Or.inr (Or.inl hji))

omit [LinearOrder U] in
/-- A single edge term is supported on that edge and the diagonal. -/
theorem skewUnit_conj_entry_eq_zero
    (X : Matrix U U ℂ) {a b i j : U}
    (hij : i ≠ j) (hab : (i, j) ≠ (a, b))
    (hba : (j, i) ≠ (a, b)) :
    (skewUnit a b * Xᵀ * (skewUnit a b)ᴴ) i j = 0 := by
  by_cases hi : i = a ∨ i = b
  · have hj : j ≠ a ∧ j ≠ b := by
      constructor
      · intro hja
        rcases hi with hia | hib
        · exact hij (hia.trans hja.symm)
        · exact hba (Prod.ext hja hib)
      · intro hjb
        rcases hi with hia | hib
        · exact hab (Prod.ext hia hjb)
        · exact hij (hib.trans hjb.symm)
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro x _
    have hz : (skewUnit a b)ᴴ x j = 0 := by
      rw [Matrix.conjTranspose_apply, RCLike.star_def]
      simp [skewUnit_apply, Ne.symm hj.1, Ne.symm hj.2]
    rw [hz, mul_zero]
  · have hi' : i ≠ a ∧ i ≠ b := by
      simpa [not_or] using hi
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro x _
    have hz : (skewUnit a b * Xᵀ) i x = 0 := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro y _
      have hrow : skewUnit a b i y = 0 := by
        simp [skewUnit_apply, Ne.symm hi'.1, Ne.symm hi'.2]
      rw [hrow, zero_mul]
    rw [hz, zero_mul]

omit [LinearOrder U] in
/-- Every graph reduction output lies in the graph coefficient space, without
requiring the input itself to be supported on the graph. -/
theorem graphReduction_mem_graphOperatorSpace
    (E : Finset (U × U)) (X : Matrix U U ℂ) :
    graphReduction E X ∈ graphOperatorSpace E := by
  intro i j hsupport
  have hij : i ≠ j := fun h => hsupport (Or.inl h)
  rw [graphReduction, Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro e _
  refine skewUnit_conj_entry_eq_zero X hij ?_ ?_
  · intro h
    exact hsupport (Or.inr (Or.inl (h.symm ▸ e.property)))
  · intro h
    exact hsupport (Or.inr (Or.inr (h.symm ▸ e.property)))

/-- The two-layer coefficient space
`U_G = {X ⊗ p + Y ⊗ q : X,Y ∈ S_G}`. -/
def graphTwoLayerSpace (E : Finset (U × U)) :
    Submodule ℂ (Matrix (U × Fin 2) (U × Fin 2) ℂ) where
  carrier :=
    {Z | ∃ X ∈ graphOperatorSpace E, ∃ Y ∈ graphOperatorSpace E,
      Z = X ⊗ₖ qubitP + Y ⊗ₖ qubitQ}
  zero_mem' := by
    refine ⟨0, Submodule.zero_mem _, 0, Submodule.zero_mem _, ?_⟩
    simp
  add_mem' := by
    rintro Z Z' ⟨X, hX, Y, hY, rfl⟩ ⟨X', hX', Y', hY', rfl⟩
    refine ⟨X + X', Submodule.add_mem _ hX hX',
      Y + Y', Submodule.add_mem _ hY hY', ?_⟩
    rw [Matrix.add_kronecker, Matrix.add_kronecker]
    abel
  smul_mem' := by
    rintro c Z ⟨X, hX, Y, hY, rfl⟩
    refine ⟨c • X, Submodule.smul_mem _ c hX,
      c • Y, Submodule.smul_mem _ c hY, ?_⟩
    rw [Matrix.smul_kronecker, Matrix.smul_kronecker, smul_add]

omit [Fintype U] [DecidableEq U] [LinearOrder U] in
theorem mem_graphTwoLayerSpace_iff
    {E : Finset (U × U)}
    {Z : Matrix (U × Fin 2) (U × Fin 2) ℂ} :
    Z ∈ graphTwoLayerSpace E
      ↔ ∃ X ∈ graphOperatorSpace E, ∃ Y ∈ graphOperatorSpace E,
        Z = X ⊗ₖ qubitP + Y ⊗ₖ qubitQ :=
  Iff.rfl

omit [Fintype U] [LinearOrder U] in
/-- The two-layer coefficient space is unital. -/
theorem one_mem_graphTwoLayerSpace (E : Finset (U × U)) :
    (1 : Matrix (U × Fin 2) (U × Fin 2) ℂ)
      ∈ graphTwoLayerSpace E := by
  refine ⟨1, one_mem_graphOperatorSpace E,
    1, one_mem_graphOperatorSpace E, ?_⟩
  rw [← Matrix.kronecker_add, qubitP_add_qubitQ,
    Matrix.one_kronecker_one]

omit [Fintype U] [DecidableEq U] [LinearOrder U] in
/-- The two-layer coefficient space is closed under conjugate transpose. -/
theorem conjTranspose_mem_graphTwoLayerSpace
    {E : Finset (U × U)}
    {Z : Matrix (U × Fin 2) (U × Fin 2) ℂ}
    (hZ : Z ∈ graphTwoLayerSpace E) :
    Zᴴ ∈ graphTwoLayerSpace E := by
  rcases hZ with ⟨X, hX, Y, hY, rfl⟩
  refine ⟨Xᴴ, conjTranspose_mem_graphOperatorSpace hX,
    Yᴴ, conjTranspose_mem_graphOperatorSpace hY, ?_⟩
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_kronecker]
  simp [qubitP, qubitQ]

omit [LinearOrder U] in
/-- The graph Kraus map preserves the two-layer coefficient space. -/
theorem graphPhiTranspose_mem_graphTwoLayerSpace
    (E : Finset (U × U))
    {Z : Matrix (U × Fin 2) (U × Fin 2) ℂ}
    (hZ : Z ∈ graphTwoLayerSpace E) :
    graphPhiTranspose E Z ∈ graphTwoLayerSpace E := by
  rcases hZ with ⟨X, -, Y, -, rfl⟩
  rw [graphPhiTranspose_layers]
  exact ⟨graphReduction E Y, graphReduction_mem_graphOperatorSpace E Y,
    graphReduction E X, graphReduction_mem_graphOperatorSpace E X, rfl⟩

omit [LinearOrder U] in
/-- The discard-and-reprepare map preserves the two-layer coefficient space. -/
theorem trace_smul_one_mem_graphTwoLayerSpace
    (E : Finset (U × U))
    (Z : Matrix (U × Fin 2) (U × Fin 2) ℂ) :
    Z.trace • (1 : Matrix (U × Fin 2) (U × Fin 2) ℂ)
      ∈ graphTwoLayerSpace E :=
  Submodule.smul_mem _ _ (one_mem_graphTwoLayerSpace E)

omit [LinearOrder U] in
/-- The corrected graph map preserves the two-layer coefficient space. -/
theorem graphTheta_mem_graphTwoLayerSpace
    (E : Finset (U × U)) (R : ℕ) (lam : ℂ)
    {Z : Matrix (U × Fin 2) (U × Fin 2) ℂ}
    (hZ : Z ∈ graphTwoLayerSpace E) :
    graphTheta E R lam Z ∈ graphTwoLayerSpace E := by
  rw [graphTheta]
  exact Submodule.add_mem _
    (graphPhiTranspose_mem_graphTwoLayerSpace E hZ)
    (Submodule.smul_mem _ lam
      (Submodule.sub_mem _
        (trace_smul_one_mem_graphTwoLayerSpace E Z)
        (Submodule.smul_mem _ (R : ℂ)⁻¹ hZ)))

end OperatorSpaces

/-! ## Matrix levels and the compressed clique input -/

section MatrixLevels

variable {L W : Type*}

/-- The `(a,b)` coefficient block of a matrix at level `L`. -/
def matrixLevelBlock
    (Z : Matrix (L × W) (L × W) ℂ) (a b : L) :
    Matrix W W ℂ :=
  Matrix.of fun x y => Z (a, x) (b, y)

/-- Matrices all of whose coefficient blocks lie in a fixed matrix subspace. -/
def matrixLevelSpace
    (S : Submodule ℂ (Matrix W W ℂ)) :
    Submodule ℂ (Matrix (L × W) (L × W) ℂ) where
  carrier := {Z | ∀ a b, matrixLevelBlock Z a b ∈ S}
  zero_mem' := by
    intro a b
    exact Submodule.zero_mem _
  add_mem' := by
    intro X Y hX hY a b
    exact Submodule.add_mem _ (hX a b) (hY a b)
  smul_mem' := by
    intro c X hX a b
    exact Submodule.smul_mem _ c (hX a b)

theorem mem_matrixLevelSpace_iff
    {S : Submodule ℂ (Matrix W W ℂ)}
    {Z : Matrix (L × W) (L × W) ℂ} :
    Z ∈ matrixLevelSpace S ↔ ∀ a b, matrixLevelBlock Z a b ∈ S :=
  Iff.rfl

end MatrixLevels

section CliqueWitness

variable {U : Type*} [Fintype U] [DecidableEq U] [LinearOrder U]

omit [Fintype U] [LinearOrder U] in
/-- A matrix unit belongs to the graph coefficient space whenever its index
pair is diagonal or is one of the two orientations of an edge. -/
theorem single_mem_graphOperatorSpace
    {E : Finset (U × U)} {i j : U}
    (hij : i = j ∨ (i, j) ∈ E ∨ (j, i) ∈ E) :
    Matrix.single i j (1 : ℂ) ∈ graphOperatorSpace E := by
  intro a b hab
  by_cases h : i = a ∧ j = b
  · rcases h with ⟨rfl, rfl⟩
    exact (hab hij).elim
  · simp [h]

/-- The vector `ξ_S` in the input `q`-layer.  Its level index is a vertex of
`S`, and that level is paired with the same ambient vertex. -/
def cliqueInputVec (S : Finset U) :
    EuclideanSpace ℂ ({i : U // i ∈ S} × (U × Fin 2)) :=
  WithLp.toLp 2 fun z =>
    if z.2.1 = z.1.val ∧ z.2.2 = 1 then 1 else 0

/-- The vector `η_S` in the output `p`-layer. -/
def cliqueOutputVec (S : Finset U) :
    EuclideanSpace ℂ ({i : U // i ∈ S} × (U × Fin 2)) :=
  WithLp.toLp 2 fun z =>
    if z.2.1 = z.1.val ∧ z.2.2 = 0 then 1 else 0

/-- The positive rank-one compressed clique input `Y_S = |ξ_S⟩⟨ξ_S|`. -/
noncomputable def cliqueLayerWitness (S : Finset U) :
    Matrix ({i : U // i ∈ S} × (U × Fin 2))
      ({i : U // i ∈ S} × (U × Fin 2)) ℂ :=
  rankOne (cliqueInputVec S) (cliqueInputVec S)

omit [Fintype U] [LinearOrder U] in
/-- Each coefficient block of `Y_S` is `E_{ab} ⊗ q`. -/
theorem matrixLevelBlock_cliqueLayerWitness
    (S : Finset U) (a b : {i : U // i ∈ S}) :
    matrixLevelBlock (cliqueLayerWitness S) a b
      = Matrix.single a.val b.val (1 : ℂ) ⊗ₖ qubitQ := by
  ext x y
  obtain ⟨i, c⟩ := x
  obtain ⟨j, d⟩ := y
  fin_cases c <;> fin_cases d
  all_goals
    simp [matrixLevelBlock, cliqueLayerWitness, rankOne,
      cliqueInputVec, Matrix.kroneckerMap_apply, qubitQ,
      Matrix.single_apply]
  all_goals aesop

omit [LinearOrder U] in
/-- The compressed clique input is positive semidefinite. -/
theorem cliqueLayerWitness_posSemidef (S : Finset U) :
    Matrix.PosSemidef (cliqueLayerWitness S) := by
  have h :
      cliqueLayerWitness S =
        Matrix.vecMulVec
          (cliqueInputVec S :
            ({i : U // i ∈ S} × (U × Fin 2)) → ℂ)
          (star (cliqueInputVec S :
            ({i : U // i ∈ S} × (U × Fin 2)) → ℂ)) := by
    ext p q
    simp [cliqueLayerWitness, rankOne, Matrix.vecMulVec_apply,
      Pi.star_apply, RCLike.star_def]
  rw [h]
  exact Matrix.posSemidef_vecMulVec_self_star _

omit [Fintype U] in
/-- A clique makes every coefficient block of `Y_S` belong to `U_G`. -/
theorem cliqueLayerWitness_mem_matrixLevelSpace
    {E : Finset (U × U)} {S : Finset U}
    (hcl : ∀ i ∈ S, ∀ j ∈ S, i < j → (i, j) ∈ E) :
    cliqueLayerWitness S
      ∈ matrixLevelSpace (L := {i : U // i ∈ S})
          (graphTwoLayerSpace E) := by
  intro a b
  rw [matrixLevelBlock_cliqueLayerWitness]
  have hab :
      a.val = b.val ∨ (a.val, b.val) ∈ E ∨ (b.val, a.val) ∈ E := by
    rcases lt_trichotomy a.val b.val with hlt | heq | hgt
    · exact Or.inr (Or.inl (hcl a.val a.property b.val b.property hlt))
    · exact Or.inl heq
    · exact Or.inr (Or.inr (hcl b.val b.property a.val a.property hgt))
  exact ⟨0, Submodule.zero_mem _,
    Matrix.single a.val b.val 1,
    single_mem_graphOperatorSpace hab, by simp⟩

end CliqueWitness

/-! ## The clique expectation -/

section CliqueExpectation

variable {U : Type*} [Fintype U] [DecidableEq U] [LinearOrder U]

omit [LinearOrder U] in
/-- Multiplication by a matrix unit selects one column and one row. -/
theorem mul_single_one_mul_apply
    (A B : Matrix U U ℂ) (r s i j : U) :
    (A * Matrix.single r s (1 : ℂ) * B) i j = A i r * B s j := by
  rw [Matrix.mul_apply]
  have hleft : ∀ x : U,
      (A * Matrix.single r s (1 : ℂ)) i x
        = if x = s then A i r else 0 := by
    intro x
    by_cases hxs : x = s
    · subst x
      rw [Matrix.mul_apply,
        Finset.sum_eq_single r]
      · simp
      · intro y _ hyr
        simp [Ne.symm hyr]
      · intro h
        exact (h (Finset.mem_univ _)).elim
    · rw [if_neg hxs, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro y _
      simp [Ne.symm hxs]
  rw [Finset.sum_congr rfl fun x _ => by rw [hleft x]]
  simp

omit [LinearOrder U] in
/-- A diagonal matrix unit contributes zero at its own diagonal coordinate
under one graph-reduction summand. -/
theorem skewUnit_conj_single_diag_apply_self
    (a b i : U) :
    (skewUnit a b * (Matrix.single i i (1 : ℂ))ᵀ
        * (skewUnit a b)ᴴ) i i = 0 := by
  rw [Matrix.transpose_single, mul_single_one_mul_apply]
  have hdiag : skewUnit a b i i = 0 := by
    by_cases hai : a = i <;> by_cases hbi : b = i <;>
      simp [skewUnit_apply, hai, hbi]
  rw [hdiag, zero_mul]

omit [LinearOrder U] in
/-- A diagonal coefficient block contributes zero to the clique expectation. -/
theorem graphReduction_single_diag_apply_self
    (E : Finset (U × U)) (i : U) :
    graphReduction E (Matrix.single i i (1 : ℂ)) i i = 0 := by
  rw [graphReduction, Matrix.sum_apply]
  exact Finset.sum_eq_zero fun e _ =>
    skewUnit_conj_single_diag_apply_self e.val.1 e.val.2 i

/-- For an increasingly oriented edge `(i,j)`, its coefficient matrix
contributes `-1` to the corresponding off-diagonal clique expectation. -/
theorem graphReduction_single_apply_of_lt
    {E : Finset (U × U)} (hE : ∀ p ∈ E, p.1 < p.2)
    {i j : U} (hij : i < j) (hmem : (i, j) ∈ E) :
    graphReduction E (Matrix.single i j (1 : ℂ)) i j = -1 := by
  rw [graphReduction, Matrix.sum_apply,
    Finset.sum_eq_single
      (⟨(i, j), hmem⟩ : {p : U × U // p ∈ E})]
  · rw [Matrix.transpose_single, mul_single_one_mul_apply]
    simp [skewUnit_apply, Matrix.conjTranspose_apply,
      ne_of_lt hij, Ne.symm (ne_of_lt hij)]
  · intro e _ hne
    apply skewUnit_conj_entry_eq_zero
      (Matrix.single i j (1 : ℂ)) (ne_of_lt hij)
    · intro h
      exact hne (Subtype.ext h.symm)
    · intro h
      have he : e.val.1 < e.val.2 := hE e.val e.property
      have hfst : j = e.val.1 := congrArg Prod.fst h
      have hsnd : i = e.val.2 := congrArg Prod.snd h
      rw [← hfst, ← hsnd] at he
      exact (asymm hij he).elim
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- The same contribution when the displayed coefficient is in decreasing
order and the graph stores the reverse increasing edge. -/
theorem graphReduction_single_apply_of_gt
    {E : Finset (U × U)} (hE : ∀ p ∈ E, p.1 < p.2)
    {i j : U} (hji : j < i) (hmem : (j, i) ∈ E) :
    graphReduction E (Matrix.single i j (1 : ℂ)) i j = -1 := by
  rw [graphReduction, Matrix.sum_apply,
    Finset.sum_eq_single
      (⟨(j, i), hmem⟩ : {p : U × U // p ∈ E})]
  · rw [Matrix.transpose_single, mul_single_one_mul_apply]
    simp [skewUnit_apply, Matrix.conjTranspose_apply,
      ne_of_lt hji, Ne.symm (ne_of_lt hji)]
  · intro e _ hne
    apply skewUnit_conj_entry_eq_zero
      (Matrix.single i j (1 : ℂ)) (Ne.symm (ne_of_lt hji))
    · intro h
      have he : e.val.1 < e.val.2 := hE e.val e.property
      have hfst : i = e.val.1 := congrArg Prod.fst h
      have hsnd : j = e.val.2 := congrArg Prod.snd h
      rw [← hfst, ← hsnd] at he
      exact (asymm hji he).elim
    · intro h
      exact hne (Subtype.ext h.symm)
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- Inside a clique, every off-diagonal coefficient contributes `-1` and every
diagonal coefficient contributes zero. -/
theorem graphReduction_single_clique_apply
    {E : Finset (U × U)} (hE : ∀ p ∈ E, p.1 < p.2)
    {S : Finset U}
    (hcl : ∀ i ∈ S, ∀ j ∈ S, i < j → (i, j) ∈ E)
    (a b : {i : U // i ∈ S}) :
    graphReduction E (Matrix.single a.val b.val (1 : ℂ)) a.val b.val
      = if a = b then 0 else -1 := by
  rcases lt_trichotomy a.val b.val with hlt | heq | hgt
  · rw [if_neg (fun hab => ne_of_lt hlt (congrArg Subtype.val hab))]
    exact graphReduction_single_apply_of_lt hE hlt
      (hcl a.val a.property b.val b.property hlt)
  · have hab : a = b := Subtype.ext heq
    subst b
    rw [if_pos rfl]
    exact graphReduction_single_diag_apply_self E a.val
  · rw [if_neg (fun hab => ne_of_gt hgt (congrArg Subtype.val hab))]
    exact graphReduction_single_apply_of_gt hE hgt
      (hcl b.val b.property a.val a.property hgt)

/-- The actual matrix-level image of the compressed clique input. -/
noncomputable def graphThetaCliqueOutput
    (E : Finset (U × U)) (R : ℕ) (lam : ℂ) (S : Finset U) :
    Matrix ({i : U // i ∈ S} × (U × Fin 2))
      ({i : U // i ∈ S} × (U × Fin 2)) ℂ :=
  mapAmplification (A := {i : U // i ∈ S})
    (graphTheta E R lam) (cliqueLayerWitness S)

omit [LinearOrder U] in
/-- The `(a,b)` output block is the corrected graph map applied to
`E_{ab} ⊗ q`. -/
theorem matrixLevelBlock_graphThetaCliqueOutput
    (E : Finset (U × U)) (R : ℕ) (lam : ℂ) (S : Finset U)
    (a b : {i : U // i ∈ S}) :
    matrixLevelBlock (graphThetaCliqueOutput E R lam S) a b
      =
    graphTheta E R lam
      (Matrix.single a.val b.val (1 : ℂ) ⊗ₖ qubitQ) := by
  change
    graphTheta E R lam
        (matrixLevelBlock (cliqueLayerWitness S) a b)
      =
    graphTheta E R lam
      (Matrix.single a.val b.val (1 : ℂ) ⊗ₖ qubitQ)
  rw [matrixLevelBlock_cliqueLayerWitness]

omit [LinearOrder U] in
/-- On the tested `p`-layer, the protected `-id/R` term vanishes and the
discard term contributes only on diagonal coefficient blocks. -/
theorem graphTheta_singleQ_apply_p
    (E : Finset (U × U)) (R : ℕ) (lam : ℂ) (i j : U) :
    graphTheta E R lam
        (Matrix.single i j (1 : ℂ) ⊗ₖ qubitQ)
        (i, 0) (j, 0)
      =
    graphReduction E (Matrix.single i j (1 : ℂ)) i j
      + lam * (if i = j then 1 else 0) := by
  have hinput :
      Matrix.single i j (1 : ℂ) ⊗ₖ qubitQ
        =
      (0 : Matrix U U ℂ) ⊗ₖ qubitP
        + Matrix.single i j (1 : ℂ) ⊗ₖ qubitQ := by simp
  have htrace :
      (Matrix.single i j (1 : ℂ)).trace
        = if i = j then 1 else 0 := by
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl]
      exact Matrix.trace_single_eq_same i (1 : ℂ)
    · rw [if_neg hij]
      exact Matrix.trace_single_eq_of_ne i j (1 : ℂ) hij
  rw [hinput, graphTheta_layers]
  simp [Matrix.kroneckerMap_apply, Matrix.add_apply,
    Matrix.sub_apply, Matrix.smul_apply,
    qubitP, qubitQ, htrace]
  by_cases hij : i = j <;> simp [hij]

omit [LinearOrder U] in
/-- Testing a matrix against `η_S` selects the diagonal ambient coordinate in
the `p`-layer of every coefficient block. -/
theorem qform_cliqueOutputVec
    (S : Finset U)
    (Z : Matrix ({i : U // i ∈ S} × (U × Fin 2))
      ({i : U // i ∈ S} × (U × Fin 2)) ℂ) :
    qform Z (cliqueOutputVec S)
      =
    ∑ a : {i : U // i ∈ S}, ∑ b : {i : U // i ∈ S},
      Z (a, (a.val, 0)) (b, (b.val, 0)) := by
  simp only [qform, Fintype.sum_prod_type, cliqueOutputVec,
    apply_ite (starRingEnd ℂ), map_one, map_zero,
    ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  simp

/-- Each diagonal level pair contributes `λ`; each ordered off-diagonal clique
pair contributes `-1`. -/
theorem graphThetaCliqueOutput_entry
    {E : Finset (U × U)} (hE : ∀ p ∈ E, p.1 < p.2)
    {S : Finset U}
    (hcl : ∀ i ∈ S, ∀ j ∈ S, i < j → (i, j) ∈ E)
    (R : ℕ) (lam : ℂ) (a b : {i : U // i ∈ S}) :
    graphThetaCliqueOutput E R lam S
        (a, (a.val, 0)) (b, (b.val, 0))
      = if a = b then lam else -1 := by
  change
    matrixLevelBlock (graphThetaCliqueOutput E R lam S) a b
        (a.val, 0) (b.val, 0)
      = if a = b then lam else -1
  rw [matrixLevelBlock_graphThetaCliqueOutput,
    graphTheta_singleQ_apply_p,
    graphReduction_single_clique_apply hE hcl]
  by_cases hab : a = b
  · subst b
    simp
  · have habv : a.val ≠ b.val := fun h => hab (Subtype.ext h)
    simp [hab, habv]

omit [Fintype U] [DecidableEq U] [LinearOrder U] in
/-- Count the diagonal and ordered off-diagonal pairs of a finite type. -/
theorem sum_if_eq_else_neg_one
    {A : Type*} [Fintype A] [DecidableEq A] (lam : ℂ) :
    (∑ a : A, ∑ b : A, if a = b then lam else -1)
      =
    (Fintype.card A : ℂ)
      * (lam - ((Fintype.card A : ℂ) - 1)) := by
  calc
    (∑ a : A, ∑ b : A, if a = b then lam else -1)
        =
      ∑ a : A, ∑ b : A,
        (-1 + if a = b then lam + 1 else 0) := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          by_cases hab : a = b <;> simp [hab]
    _ = ∑ _a : A,
          ((Fintype.card A : ℂ) * (-1) + (lam + 1)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_add_distrib]
      simp
    _ = (Fintype.card A : ℂ)
          * (lam - ((Fintype.card A : ℂ) - 1)) := by
      simp
      ring

/-- **Compressed clique expectation** (`eq:witness-val`).

The value is independent of the protected rank parameter `R`: the input lies
in the `q`-layer and the test vector in the `p`-layer, so the `-id/R` term is
orthogonal to the test. -/
theorem qform_graphThetaCliqueOutput
    {E : Finset (U × U)} (hE : ∀ p ∈ E, p.1 < p.2)
    {S : Finset U}
    (hcl : ∀ i ∈ S, ∀ j ∈ S, i < j → (i, j) ∈ E)
    (R : ℕ) (lam : ℂ) :
    qform (graphThetaCliqueOutput E R lam S) (cliqueOutputVec S)
      =
    (S.card : ℂ) * (lam - ((S.card : ℂ) - 1)) := by
  rw [qform_cliqueOutputVec]
  simp_rw [graphThetaCliqueOutput_entry hE hcl]
  rw [sum_if_eq_else_neg_one]
  simp

end CliqueExpectation

end RankR
