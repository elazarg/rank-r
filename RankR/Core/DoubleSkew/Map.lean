/-
The double-skew Kraus map `Φ` on `(U ⊗ V) ⊗ Q`.

The map `Λ_E(X) = Tr(X) I - Xᵀ` on a single factor has Choi operator `I - F`,
whose range is the antisymmetric subspace; its Kraus operators are therefore the
elementary skew-symmetric matrices `E_{ab} - E_{ba}`.  Tensoring the two factors
and acting trivially on `Q` gives `Λ_U ⊗ Λ_V ⊗ id_Q`, realized here as the Kraus
sum over the unordered family `(a, b, c, d) ↦ (E_{ab} - E_{ba}) ⊗ (E_{cd} - E_{dc})`.

Because the family is indexed by *all* of `U × U` and `V × V`, and because
`L_{ba} = -L_{ab}` while `L_{aa} = 0`, each unordered pair is counted twice on
each factor: the resulting map is four times the map obtained from a family
indexed by ordered pairs `a < b`.  It is therefore named `Phi4`.

The placement `A ↦ A ⊗ I_Q` that carries an operator onto the doubled space is
recorded for a single space `W`, together with its linearity and the entries of
the conjugation `Y ↦ (A ⊗ I_Q) Y (A ⊗ I_Q)ᴴ`.  `Φ` is the instance at
`W = U ⊗ V`, and it is the kernel computation below — four terms carried by
Kronecker deltas on the `U` and `V` labels separately — that is genuinely
bipartite.
-/
import RankR.Core.Amplification.Sectors
import RankR.Core.DoubleSkew.Basic
import RankR.Library.Matrix.Placement

namespace RankR

open Matrix Finset ComplexConjugate
open scoped Kronecker

/-! ## Elementary sum manipulations -/

section Sums

variable {Z : Type*} [Fintype Z] [DecidableEq Z]

/-- Collapse of a Kronecker delta whose summation index sits on the right. -/
theorem sum_ite_one_mul (c : Z) (f : Z → ℂ) :
    ∑ z, (if c = z then (1 : ℂ) else 0) * f z = f c := by
  simp

/-- Collapse of a Kronecker delta whose summation index sits on the left. -/
theorem sum_ite_one_mul' (c : Z) (f : Z → ℂ) :
    ∑ z, (if z = c then (1 : ℂ) else 0) * f z = f c := by
  simp

/-- **Collapse of a sum against an antisymmetrized Kronecker delta.**  The two
delta terms pick out `z = c₂` and `z = c₁` respectively, and each surviving
factor is the delta of the indices left over.

The double-skew kernel is a product of one such factor per side, so this is
applied once on `U` and once on `V`; nothing distinguishes the two beyond which
index type is being summed. -/
theorem sum_antisym_collapse_factor (a : ℂ) (c₀ c₁ c₂ : Z) (f : Z → ℂ) :
    ∑ z : Z, (a * ((if c₀ = c₁ then (1 : ℂ) else 0) * (if c₂ = z then 1 else 0)
        - (if c₀ = z then (1 : ℂ) else 0) * (if c₂ = c₁ then 1 else 0))) * f z
      = a * ((if c₀ = c₁ then (1 : ℂ) else 0) * f c₂
           - (if c₂ = c₁ then (1 : ℂ) else 0) * f c₀) := by
  have hterm : ∀ z : Z, (a * ((if c₀ = c₁ then (1 : ℂ) else 0) * (if c₂ = z then 1 else 0)
        - (if c₀ = z then (1 : ℂ) else 0) * (if c₂ = c₁ then 1 else 0))) * f z
      = (if c₂ = z then (1 : ℂ) else 0) * (a * (if c₀ = c₁ then (1 : ℂ) else 0) * f z)
        - (if c₀ = z then (1 : ℂ) else 0)
            * (a * (if c₂ = c₁ then (1 : ℂ) else 0) * f z) :=
    fun z => by ring
  rw [Finset.sum_congr rfl fun z _ => hterm z, Finset.sum_sub_distrib, sum_ite_one_mul,
    sum_ite_one_mul]
  ring

/-- A double sum whose summand splits as a product of one factor per index. -/
theorem sum_sum_mul {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι → ℂ) (g : κ → ℂ) :
    ∑ a : ι, ∑ b : κ, f a * g b = (∑ a, f a) * (∑ b, g b) :=
  (Fintype.sum_mul_sum f g).symm

end Sums

/-! ## The Kraus coefficient of the double-skew family -/

section SkewSums

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The Gram-type sum of the elementary skew matrices over *all* index pairs is
twice an antisymmetrized Kronecker delta. -/
theorem sum_skewUnit_mul_conj (α γ α' γ' : W) :
    ∑ p : W × W, skewUnit p.1 p.2 α γ * conj (skewUnit p.1 p.2 α' γ')
      = 2 * ((if α = α' then (1 : ℂ) else 0) * (if γ = γ' then 1 else 0)
           - (if α = γ' then (1 : ℂ) else 0) * (if γ = α' then 1 else 0)) := by
  have key : ∀ X X' : W,
      ∑ z : W, (if z = X then (1 : ℂ) else 0) * (if z = X' then (1 : ℂ) else 0)
        = if X = X' then 1 else 0 := fun X X' => sum_ite_one_mul' X _
  have hprod : ∀ X X' : W, ∀ Y Y' : W,
      ∑ a : W, ∑ b : W,
          ((if a = X then (1 : ℂ) else 0) * (if a = X' then 1 else 0))
            * ((if b = Y then (1 : ℂ) else 0) * (if b = Y' then 1 else 0))
        = (if X = X' then (1 : ℂ) else 0) * (if Y = Y' then 1 else 0) := by
    intro X X' Y Y'
    rw [sum_sum_mul (fun a : W => (if a = X then (1 : ℂ) else 0) * (if a = X' then 1 else 0))
        (fun b : W => (if b = Y then (1 : ℂ) else 0) * (if b = Y' then 1 else 0)), key, key]
  have expand : ∀ a b : W, skewUnit a b α γ * conj (skewUnit a b α' γ')
      = ((if a = α then (1 : ℂ) else 0) * (if a = α' then 1 else 0))
          * ((if b = γ then (1 : ℂ) else 0) * (if b = γ' then 1 else 0))
        - ((if a = α then (1 : ℂ) else 0) * (if a = γ' then 1 else 0))
          * ((if b = γ then (1 : ℂ) else 0) * (if b = α' then 1 else 0))
        - ((if a = γ then (1 : ℂ) else 0) * (if a = α' then 1 else 0))
          * ((if b = α then (1 : ℂ) else 0) * (if b = γ' then 1 else 0))
        + ((if a = γ then (1 : ℂ) else 0) * (if a = γ' then 1 else 0))
          * ((if b = α then (1 : ℂ) else 0) * (if b = α' then 1 else 0)) := by
    intro a b
    rw [skewUnit_apply, skewUnit_apply]
    simp only [map_sub, map_mul, apply_ite conj, map_one, map_zero]
    ring
  rw [Fintype.sum_prod_type,
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => expand a b]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hprod, hprod, hprod, hprod]
  ring

end SkewSums

/-! ## The map `Φ` -/

section Kron

variable {U V : Type*}

/-- Entries of a Kronecker product, for indices that are not literal pairs. -/
theorem kron_apply (A : Matrix U U ℂ) (B : Matrix V V ℂ) (u v : U × V) :
    (A ⊗ₖ B) u v = A u.1 v.1 * B u.2 v.2 := rfl

end Kron

section Phi

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] {s : ℕ}

/-- The Kraus coefficient of the double-skew family: the product of two
antisymmetrized Kronecker deltas, each carrying a factor `2`. -/
theorem sum_kron_coeff (u v u' v' : U × V) :
    ∑ p : (U × U) × (V × V),
        (skewUnit p.1.1 p.1.2 ⊗ₖ skewUnit p.2.1 p.2.2) u v
          * conj ((skewUnit p.1.1 p.1.2 ⊗ₖ skewUnit p.2.1 p.2.2) u' v')
      = (2 * ((if u.1 = u'.1 then (1 : ℂ) else 0) * (if v.1 = v'.1 then 1 else 0)
            - (if u.1 = v'.1 then (1 : ℂ) else 0) * (if v.1 = u'.1 then 1 else 0)))
        * (2 * ((if u.2 = u'.2 then (1 : ℂ) else 0) * (if v.2 = v'.2 then 1 else 0)
            - (if u.2 = v'.2 then (1 : ℂ) else 0) * (if v.2 = u'.2 then 1 else 0))) := by
  calc ∑ p : (U × U) × (V × V),
        (skewUnit p.1.1 p.1.2 ⊗ₖ skewUnit p.2.1 p.2.2) u v
          * conj ((skewUnit p.1.1 p.1.2 ⊗ₖ skewUnit p.2.1 p.2.2) u' v')
      = ∑ a : U × U, ∑ c : V × V,
          (skewUnit a.1 a.2 u.1 v.1 * conj (skewUnit a.1 a.2 u'.1 v'.1))
            * (skewUnit c.1 c.2 u.2 v.2 * conj (skewUnit c.1 c.2 u'.2 v'.2)) := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
        rw [kron_apply, kron_apply, map_mul]
        ring
    _ = (∑ a : U × U, skewUnit a.1 a.2 u.1 v.1 * conj (skewUnit a.1 a.2 u'.1 v'.1))
          * (∑ c : V × V, skewUnit c.1 c.2 u.2 v.2 * conj (skewUnit c.1 c.2 u'.2 v'.2)) :=
        sum_sum_mul _ _
    _ = _ := by rw [sum_skewUnit_mul_conj, sum_skewUnit_mul_conj]

/-- `Λ_U ⊗ Λ_V ⊗ id_Q`, scaled by `4`: the Kraus sum over the double-skew family
indexed by all of `U × U` and `V × V`. -/
noncomputable def Phi4 (Y : Matrix ((U × V) × Fin s) ((U × V) × Fin s) ℂ) :
    Matrix ((U × V) × Fin s) ((U × V) × Fin s) ℂ :=
  krausSum (fun p : (U × U) × (V × V) =>
    placeT (skewUnit p.1.1 p.1.2 ⊗ₖ skewUnit p.2.1 p.2.2)) Y

/-- `Phi4` preserves positive semidefiniteness, being a Kraus sum. -/
theorem qform_Phi4_nonneg {Y : Matrix ((U × V) × Fin s) ((U × V) × Fin s) ℂ}
    (hY : ∀ z : EuclideanSpace ℂ ((U × V) × Fin s), 0 ≤ (qform Y z).re)
    (x : EuclideanSpace ℂ ((U × V) × Fin s)) : 0 ≤ (qform (Phi4 Y) x).re :=
  qform_krausSum_nonneg _ hY x

/-- `Phi4` commutes with subtraction. -/
theorem Phi4_sub (Y Z : Matrix ((U × V) × Fin s) ((U × V) × Fin s) ℂ) :
    Phi4 (Y - Z) = Phi4 Y - Phi4 Z := by
  simp only [Phi4, krausSum, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]

/-- `Phi4` commutes with scalar multiplication. -/
theorem Phi4_smul (c : ℂ) (Y : Matrix ((U × V) × Fin s) ((U × V) × Fin s) ℂ) :
    Phi4 (c • Y) = c • Phi4 Y := by
  simp only [Phi4, krausSum, Matrix.mul_smul, Matrix.smul_mul, ← Finset.smul_sum]

/-- Entries of `Phi4 Y` before the Kronecker deltas are collapsed. -/
theorem Phi4_apply_aux (Y : Matrix ((U × V) × Fin s) ((U × V) × Fin s) ℂ)
    (x y : (U × V) × Fin s) :
    Phi4 Y x y = ∑ q : U × V, ∑ q' : U × V,
      ((2 * ((if x.1.1 = y.1.1 then (1 : ℂ) else 0) * (if q.1 = q'.1 then 1 else 0)
           - (if x.1.1 = q'.1 then (1 : ℂ) else 0) * (if q.1 = y.1.1 then 1 else 0)))
        * (2 * ((if x.1.2 = y.1.2 then (1 : ℂ) else 0) * (if q.2 = q'.2 then 1 else 0)
           - (if x.1.2 = q'.2 then (1 : ℂ) else 0) * (if q.2 = y.1.2 then 1 else 0))))
        * Y (q, x.2) (q', y.2) := by
  have h1 : Phi4 Y x y = ∑ p : (U × U) × (V × V), ∑ q : U × V, ∑ q' : U × V,
      (skewUnit p.1.1 p.1.2 ⊗ₖ skewUnit p.2.1 p.2.2) x.1 q * Y (q, x.2) (q', y.2)
        * conj ((skewUnit p.1.1 p.1.2 ⊗ₖ skewUnit p.2.1 p.2.2) y.1 q') := by
    simp only [Phi4, krausSum, Matrix.sum_apply, placeT_conj_apply]
  rw [h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q' _ => ?_
  rw [← sum_kron_coeff x.1 q y.1 q', Finset.sum_mul]
  exact Finset.sum_congr rfl fun p _ => by ring

/-- Collapse of the inner double sum against the product of the two
antisymmetrized Kronecker deltas. -/
theorem sum_antisym_collapse (c : ℂ) (α α' γ : U) (β β' δ : V) (H : U → V → ℂ) :
    ∑ γ' : U, ∑ δ' : V,
        ((c * ((if α = α' then (1 : ℂ) else 0) * (if γ = γ' then 1 else 0)
             - (if α = γ' then (1 : ℂ) else 0) * (if γ = α' then 1 else 0)))
          * ((if β = β' then (1 : ℂ) else 0) * (if δ = δ' then 1 else 0)
             - (if β = δ' then (1 : ℂ) else 0) * (if δ = β' then 1 else 0))) * H γ' δ'
      = c * ((if α = α' then (1 : ℂ) else 0)
              * ((if β = β' then (1 : ℂ) else 0) * H γ δ
                 - (if δ = β' then (1 : ℂ) else 0) * H γ β)
            - (if γ = α' then (1 : ℂ) else 0)
              * ((if β = β' then (1 : ℂ) else 0) * H α δ
                 - (if δ = β' then (1 : ℂ) else 0) * H α β)) := by
  have h1 : ∀ γ' : U, ∑ δ' : V,
      ((c * ((if α = α' then (1 : ℂ) else 0) * (if γ = γ' then 1 else 0)
           - (if α = γ' then (1 : ℂ) else 0) * (if γ = α' then 1 else 0)))
        * ((if β = β' then (1 : ℂ) else 0) * (if δ = δ' then 1 else 0)
           - (if β = δ' then (1 : ℂ) else 0) * (if δ = β' then 1 else 0))) * H γ' δ'
      = (c * ((if α = α' then (1 : ℂ) else 0) * (if γ = γ' then 1 else 0)
           - (if α = γ' then (1 : ℂ) else 0) * (if γ = α' then 1 else 0)))
        * ((if β = β' then (1 : ℂ) else 0) * H γ' δ
           - (if δ = β' then (1 : ℂ) else 0) * H γ' β) :=
    fun γ' => sum_antisym_collapse_factor _ β β' δ (H γ')
  rw [Finset.sum_congr rfl fun γ' _ => h1 γ']
  exact sum_antisym_collapse_factor c α α' γ _

/-- Collapse of the outer double sum, after the inner one has been collapsed. -/
theorem sum_outer_collapse (α α' : U) (β β' : V) (G : U → V → U → V → ℂ) :
    ∑ γ : U, ∑ δ : V,
        ((if α = α' then (1 : ℂ) else 0)
            * ((if β = β' then (1 : ℂ) else 0) * G γ δ γ δ
               - (if δ = β' then (1 : ℂ) else 0) * G γ δ γ β)
          - (if γ = α' then (1 : ℂ) else 0)
            * ((if β = β' then (1 : ℂ) else 0) * G γ δ α δ
               - (if δ = β' then (1 : ℂ) else 0) * G γ δ α β))
      = (if α = α' then (1 : ℂ) else 0) * (if β = β' then (1 : ℂ) else 0)
            * (∑ γ : U, ∑ δ : V, G γ δ γ δ)
        - (if α = α' then (1 : ℂ) else 0) * (∑ γ : U, G γ β' γ β)
        - (if β = β' then (1 : ℂ) else 0) * (∑ δ : V, G α' δ α δ)
        + G α' β' α β := by
  have h1 : ∑ γ : U, ∑ δ : V,
      ((if α = α' then (1 : ℂ) else 0) * (if β = β' then (1 : ℂ) else 0)) * G γ δ γ δ
      = (if α = α' then (1 : ℂ) else 0) * (if β = β' then (1 : ℂ) else 0)
          * (∑ γ : U, ∑ δ : V, G γ δ γ δ) := by
    simp only [Finset.mul_sum]
  have h2 : ∑ γ : U, ∑ δ : V,
      ((if α = α' then (1 : ℂ) else 0) * (if δ = β' then (1 : ℂ) else 0)) * G γ δ γ β
      = (if α = α' then (1 : ℂ) else 0) * (∑ γ : U, G γ β' γ β) := by
    conv_rhs => rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    have hterm : ∀ δ : V,
        ((if α = α' then (1 : ℂ) else 0) * (if δ = β' then (1 : ℂ) else 0)) * G γ δ γ β
        = (if δ = β' then (1 : ℂ) else 0) * ((if α = α' then (1 : ℂ) else 0) * G γ δ γ β) :=
      fun δ => by ring
    rw [Finset.sum_congr rfl fun δ _ => hterm δ, sum_ite_one_mul']
  have h3 : ∑ γ : U, ∑ δ : V,
      ((if γ = α' then (1 : ℂ) else 0) * (if β = β' then (1 : ℂ) else 0)) * G γ δ α δ
      = (if β = β' then (1 : ℂ) else 0) * (∑ δ : V, G α' δ α δ) := by
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun δ _ => ?_
    have hterm : ∀ γ : U,
        ((if γ = α' then (1 : ℂ) else 0) * (if β = β' then (1 : ℂ) else 0)) * G γ δ α δ
        = (if γ = α' then (1 : ℂ) else 0) * ((if β = β' then (1 : ℂ) else 0) * G γ δ α δ) :=
      fun γ => by ring
    rw [Finset.sum_congr rfl fun γ _ => hterm γ, sum_ite_one_mul']
  have h4 : ∑ γ : U, ∑ δ : V,
      ((if γ = α' then (1 : ℂ) else 0) * (if δ = β' then (1 : ℂ) else 0)) * G γ δ α β
      = G α' β' α β := by
    have hin : ∀ γ : U, ∑ δ : V,
        ((if γ = α' then (1 : ℂ) else 0) * (if δ = β' then (1 : ℂ) else 0)) * G γ δ α β
        = (if γ = α' then (1 : ℂ) else 0) * G γ β' α β := by
      intro γ
      have hterm : ∀ δ : V,
          ((if γ = α' then (1 : ℂ) else 0) * (if δ = β' then (1 : ℂ) else 0)) * G γ δ α β
          = (if δ = β' then (1 : ℂ) else 0) * ((if γ = α' then (1 : ℂ) else 0) * G γ δ α β) :=
        fun δ => by ring
      rw [Finset.sum_congr rfl fun δ _ => hterm δ, sum_ite_one_mul']
    rw [Finset.sum_congr rfl fun γ _ => hin γ, sum_ite_one_mul']
  have hsplit : ∀ (γ : U) (δ : V),
      ((if α = α' then (1 : ℂ) else 0)
          * ((if β = β' then (1 : ℂ) else 0) * G γ δ γ δ
             - (if δ = β' then (1 : ℂ) else 0) * G γ δ γ β)
        - (if γ = α' then (1 : ℂ) else 0)
          * ((if β = β' then (1 : ℂ) else 0) * G γ δ α δ
             - (if δ = β' then (1 : ℂ) else 0) * G γ δ α β))
      = ((if α = α' then (1 : ℂ) else 0) * (if β = β' then (1 : ℂ) else 0)) * G γ δ γ δ
        - ((if α = α' then (1 : ℂ) else 0) * (if δ = β' then (1 : ℂ) else 0)) * G γ δ γ β
        - ((if γ = α' then (1 : ℂ) else 0) * (if β = β' then (1 : ℂ) else 0)) * G γ δ α δ
        + ((if γ = α' then (1 : ℂ) else 0) * (if δ = β' then (1 : ℂ) else 0)) * G γ δ α β :=
    fun γ δ => by ring
  rw [Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun δ _ => hsplit γ δ]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [h1, h2, h3, h4]

/-- **The kernel of `Phi4`**: four terms, the first three carried by Kronecker
deltas on the `U` and `V` labels and the last one unrestricted. -/
theorem Phi4_apply (Y : Matrix ((U × V) × Fin s) ((U × V) × Fin s) ℂ) (x y : (U × V) × Fin s) :
    Phi4 Y x y
      = 4 * ((if x.1.1 = y.1.1 ∧ x.1.2 = y.1.2 then ∑ q : U × V, Y (q, x.2) (q, y.2) else 0)
           - (if x.1.1 = y.1.1 then ∑ g : U, Y ((g, y.1.2), x.2) ((g, x.1.2), y.2) else 0)
           - (if x.1.2 = y.1.2 then ∑ h : V, Y ((y.1.1, h), x.2) ((x.1.1, h), y.2) else 0)
           + Y ((y.1.1, y.1.2), x.2) ((x.1.1, x.1.2), y.2)) := by
  rw [Phi4_apply_aux]
  simp only [Fintype.sum_prod_type]
  have hre : ∀ (γ : U) (δ : V) (γ' : U) (δ' : V),
      ((2 * ((if x.1.1 = y.1.1 then (1 : ℂ) else 0) * (if γ = γ' then 1 else 0)
           - (if x.1.1 = γ' then (1 : ℂ) else 0) * (if γ = y.1.1 then 1 else 0)))
        * (2 * ((if x.1.2 = y.1.2 then (1 : ℂ) else 0) * (if δ = δ' then 1 else 0)
           - (if x.1.2 = δ' then (1 : ℂ) else 0) * (if δ = y.1.2 then 1 else 0))))
        * Y ((γ, δ), x.2) ((γ', δ'), y.2)
      = ((4 * ((if x.1.1 = y.1.1 then (1 : ℂ) else 0) * (if γ = γ' then 1 else 0)
             - (if x.1.1 = γ' then (1 : ℂ) else 0) * (if γ = y.1.1 then 1 else 0)))
          * ((if x.1.2 = y.1.2 then (1 : ℂ) else 0) * (if δ = δ' then 1 else 0)
             - (if x.1.2 = δ' then (1 : ℂ) else 0) * (if δ = y.1.2 then 1 else 0)))
        * Y ((γ, δ), x.2) ((γ', δ'), y.2) := fun γ δ γ' δ' => by ring
  simp only [hre]
  have hinner : ∀ (γ : U) (δ : V), ∑ γ' : U, ∑ δ' : V,
      ((4 * ((if x.1.1 = y.1.1 then (1 : ℂ) else 0) * (if γ = γ' then 1 else 0)
           - (if x.1.1 = γ' then (1 : ℂ) else 0) * (if γ = y.1.1 then 1 else 0)))
        * ((if x.1.2 = y.1.2 then (1 : ℂ) else 0) * (if δ = δ' then 1 else 0)
           - (if x.1.2 = δ' then (1 : ℂ) else 0) * (if δ = y.1.2 then 1 else 0)))
        * Y ((γ, δ), x.2) ((γ', δ'), y.2)
      = 4 * ((if x.1.1 = y.1.1 then (1 : ℂ) else 0)
              * ((if x.1.2 = y.1.2 then (1 : ℂ) else 0) * Y ((γ, δ), x.2) ((γ, δ), y.2)
                 - (if δ = y.1.2 then (1 : ℂ) else 0) * Y ((γ, δ), x.2) ((γ, x.1.2), y.2))
            - (if γ = y.1.1 then (1 : ℂ) else 0)
              * ((if x.1.2 = y.1.2 then (1 : ℂ) else 0) * Y ((γ, δ), x.2) ((x.1.1, δ), y.2)
                 - (if δ = y.1.2 then (1 : ℂ) else 0) * Y ((γ, δ), x.2) ((x.1.1, x.1.2), y.2))) :=
    fun γ δ => sum_antisym_collapse 4 x.1.1 y.1.1 γ x.1.2 y.1.2 δ
      (fun γ' δ' => Y ((γ, δ), x.2) ((γ', δ'), y.2))
  simp only [hinner, ← Finset.mul_sum]
  rw [sum_outer_collapse x.1.1 y.1.1 x.1.2 y.1.2
    (fun γ δ γ' δ' => Y ((γ, δ), x.2) ((γ', δ'), y.2))]
  have hS : (∑ γ : U, ∑ δ : V, Y ((γ, δ), x.2) ((γ, δ), y.2))
      = ∑ q : U × V, Y (q, x.2) (q, y.2) := by rw [Fintype.sum_prod_type]
  rw [hS]
  by_cases h1 : x.1.1 = y.1.1 <;> by_cases h2 : x.1.2 = y.1.2 <;>
    simp only [h1, h2, if_false, and_true, and_false, one_mul, zero_mul, mul_one, mul_zero,
      sub_zero, zero_sub, if_pos]

end Phi

end RankR
