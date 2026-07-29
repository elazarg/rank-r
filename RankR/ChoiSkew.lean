/-
The Choi operator of the double-skew Kraus family.

`Λ_U ⊗ Λ_V` is realized in `Phi.lean` as the Kraus sum over the family
`(a,b,c,d) ↦ (E_{ab} − E_{ba}) ⊗ (E_{cd} − E_{dc})`, indexed by all of `U × U`
and `V × V`.  Its Choi operator is `16 Qm`, sixteen times the double
antisymmetrizer of `Antisym.lean`.

The factor is the product of three twos and a four.  Each factor of the family is
indexed by ordered pairs, so counts every unordered pair twice: that is the `4`
already recorded in the name `Phi4`.  The Gram sum of the elementary skew
matrices over a factor carries a further `2` (`sum_skewUnit_mul_conj`), giving
another `4` across the two factors, and `Qm` normalizes its four-term alternating
sum by `¼`.

Consequences: the two operators have the same rank-two bound up to that factor,
so Fu-Gao-Park's `‖Qm‖_{S(2)} = ½` reads `β = 4` for the family
(`choiTwoBound_skewKraus_of_FGP`), and `Qm (vec K) = vec K` for `K` in the
double-skew subspace is the statement that `vec K` is in the eigenspace of the
Choi operator at its top.
-/
import RankR.Antisym
import RankR.Choi
import RankR.Phi

namespace RankR

open Matrix Finset ComplexConjugate
open scoped Kronecker

/-- Symmetry of a Kronecker delta in its two indices. -/
private theorem ite_swap {α : Type*} [DecidableEq α] (p q : α) :
    (if p = q then (1 : ℂ) else 0) = if q = p then (1 : ℂ) else 0 := by
  by_cases h : p = q <;> simp [h, eq_comm]

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]

/-- The Kraus index of the double-skew family: an ordered pair of indices on each
of the two factors. -/
abbrev KIdx (U V : Type*) := (U × U) × (V × V)

/-- The Kraus operators of `Λ_U ⊗ Λ_V`: elementary tensors of the elementary
skew-symmetric matrices. -/
noncomputable def skewKraus (f : KIdx U V) : Matrix (U × V) (U × V) ℂ :=
  skewUnit f.1.1 f.1.2 ⊗ₖ skewUnit f.2.1 f.2.2

omit [Fintype U] [Fintype V] in
/-- If the left local index type is a subsingleton, every double-skew Kraus
operator vanishes. -/
theorem skewKraus_eq_zero_of_subsingleton
    [Subsingleton U] (f : KIdx U V) :
    skewKraus f = 0 := by
  have h : f.1.1 = f.1.2 := Subsingleton.elim _ _
  rw [skewKraus, h]
  simp [skewUnit]

omit [Fintype U] [Fintype V] in
/-- Every Kraus operator of the family lies in the double-skew subspace. -/
theorem skewKraus_mem_doubleSkew (f : KIdx U V) : skewKraus f ∈ doubleSkew U V :=
  kron_mem_doubleSkew (skewUnit_isSkew _ _) (skewUnit_isSkew _ _)

omit [Fintype U] [Fintype V] in
/-- **The Kraus operators are transpose-symmetric.**  Two skew factors make a
symmetric tensor, and this is the hypothesis under which the trace correction of
`prop:operator_ineq` survives: it is what makes `⟪δ_E, 𝒯c⟫ = 0`. -/
theorem skewKraus_transpose (f : KIdx U V) : (skewKraus f)ᵀ = skewKraus f :=
  transpose_eq_self_of_mem_doubleSkew (skewKraus_mem_doubleSkew f)

/-- Four Kronecker deltas, regrouped from the `(U,V)`-pairing of `Idx` to the
`(U,U)`, `(V,V)` pairing of the two antisymmetrized slots. -/
private theorem ite_and4 {p q r s : Prop} [Decidable p] [Decidable q] [Decidable r]
    [Decidable s] :
    (if (p ∧ q) ∧ (r ∧ s) then (1 : ℂ) else 0)
      = ((if p then (1 : ℂ) else 0) * (if r then 1 else 0))
        * ((if q then (1 : ℂ) else 0) * (if s then 1 else 0)) := by
  by_cases hp : p <;> by_cases hq : q <;> by_cases hr : r <;> by_cases hs : s <;>
    simp [hp, hq, hr, hs]

omit [Fintype U] [Fintype V] in
/-- The entries of `Qm`, with the four indices separated and the Klein
four-group sum factored.

Each of the four terms of `Qm` is a `U`-condition times a `V`-condition: the
identity and `swU` share the `V`-condition, as do `swV` and `swV ∘ swU`, so the
alternating sum factors as `(same − swap)_U · (same − swap)_V`. -/
theorem Qm_apply_prod (a c a' c' : U) (b d b' d' : V) :
    (Qm : Matrix (Idx U V) (Idx U V) ℂ) ((a, b), (c, d)) ((a', b'), (c', d'))
      = (4 : ℂ)⁻¹ *
          (((if a = a' then (1 : ℂ) else 0) * (if c = c' then 1 else 0)
              - (if a = c' then (1 : ℂ) else 0) * (if c = a' then 1 else 0))
            * ((if b = b' then (1 : ℂ) else 0) * (if d = d' then 1 else 0)
              - (if b = d' then (1 : ℂ) else 0) * (if d = b' then 1 else 0))) := by
  rw [Qm_apply]
  simp only [swU, swV, Prod.mk.injEq, ite_and4]
  rw [ite_swap a a', ite_swap c c', ite_swap a c', ite_swap c a',
    ite_swap b b', ite_swap d d', ite_swap b d', ite_swap d b']
  ring

/-- **The Choi operator of the double-skew family is `16 Qm`.**

The Gram sum of the family over the Kraus index is an antisymmetrized pair of
Kronecker deltas on each factor (`sum_kron_coeff`), which is `Qm_apply_prod` up
to the constant. -/
theorem choiOf_skewKraus :
    choiOf (skewKraus (U := U) (V := V)) = (16 : ℂ) • Qm := by
  ext X Y
  obtain ⟨⟨a, b⟩, c, d⟩ := X
  obtain ⟨⟨a', b'⟩, c', d'⟩ := Y
  have hL : choiOf (skewKraus (U := U) (V := V)) ((a, b), (c, d)) ((a', b'), (c', d'))
      = ∑ p : KIdx U V,
          (skewUnit p.1.1 p.1.2 ⊗ₖ skewUnit p.2.1 p.2.2) (a, b) (c, d)
            * conj ((skewUnit p.1.1 p.1.2 ⊗ₖ skewUnit p.2.1 p.2.2) (a', b') (c', d')) := by
    simp [choiOf, Matrix.sum_apply, rankOne, skewKraus]
  rw [hL, sum_kron_coeff (a, b) (c, d) (a', b') (c', d'), Matrix.smul_apply,
    smul_eq_mul, Qm_apply_prod]
  ring

/-- If either factor has cardinality below two, the entire ordered Kraus family
vanishes. -/
theorem skewKraus_family_eq_zero_of_card_lt_two
    (hcard : Fintype.card U < 2 ∨ Fintype.card V < 2) :
    skewKraus (U := U) (V := V) = 0 := by
  rcases hcard with hU | hV
  · letI : Subsingleton U :=
      Fintype.card_le_one_iff_subsingleton.mp (by omega)
    funext f
    exact skewKraus_eq_zero_of_subsingleton f
  · letI : Subsingleton V :=
      Fintype.card_le_one_iff_subsingleton.mp (by omega)
    funext f
    rw [skewKraus]
    have h : f.2.1 = f.2.2 := Subsingleton.elim _ _
    rw [h]
    simp [skewUnit]

/-- In a degenerate local dimension the Choi operator of the double-skew map is
zero. -/
theorem choiOf_skewKraus_eq_zero_of_card_lt_two
    (hcard : Fintype.card U < 2 ∨ Fintype.card V < 2) :
    choiOf (skewKraus (U := U) (V := V)) = 0 := by
  rw [skewKraus_family_eq_zero_of_card_lt_two hcard]
  ext X Y
  simp [choiOf, rankOne]

/-- In a degenerate local dimension the double-skew Choi bound holds with
constant zero. -/
theorem choiTwoBound_skewKraus_zero_of_card_lt_two
    (hcard : Fintype.card U < 2 ∨ Fintype.card V < 2) :
    ChoiTwoBound (choiOf (skewKraus (U := U) (V := V))) 0 := by
  rw [choiOf_skewKraus_eq_zero_of_card_lt_two hcard]
  intro u₁ v₁ u₂ v₂
  simp [qform]

/-- The rank-two bound for the family, at `β = 4`.

`ChoiTwoBound Qm (1/4)` is Fu-Gao-Park's estimate; the Choi operator of the
family is `16` times `Qm`, so its constant is `16 · ¼ = 4`. -/
theorem choiTwoBound_skewKraus (h : ChoiTwoBound (Qm : Matrix (Idx U V) (Idx U V) ℂ) (1 / 4)) :
    ChoiTwoBound (choiOf (skewKraus (U := U) (V := V))) 4 := by
  rw [choiOf_skewKraus, show (16 : ℂ) = ((16 : ℝ) : ℂ) by norm_num,
    show (4 : ℝ) = 16 * (1 / 4) by norm_num]
  exact choiTwoBound_smul (by norm_num) h

end RankR
