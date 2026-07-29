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

namespace RankR

open Matrix Finset ComplexConjugate
open scoped Kronecker

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
    apply hsupport (Or.inr (Or.inl ?_))
    exact h.symm ▸ e.property
  · intro h
    apply hsupport (Or.inr (Or.inr ?_))
    exact h.symm ▸ e.property

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

end RankR
