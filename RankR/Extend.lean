/-
Zero-extension of operators along embeddings of the local factors.

Fu-Gao-Park state their estimate on `(ℂ^d)^{⊗4}`, all four tensor factors equal.
`RankR.FGPBound U V` quantifies over two arbitrary finite index types, so it is
strictly more general.  The two are reconciled here: an embedding `f : U ↪ U'`
of the row factor and `g : V ↪ V'` of the column factor induce a zero-extension
of operators on `U ⊗ V` to operators on `U' ⊗ V'` which preserves rank-one
decompositions, the Hilbert-Schmidt norm, and the double-antisymmetric quadratic
form.  Consequently `FGPBound` transfers *backwards* along `f` and `g`, and the
square case `FGPBound (Fin d) (Fin d)` implies every case with both local
dimensions at most `d`.
-/
import RankR.FGP

namespace RankR

open Matrix Finset ComplexConjugate

/-! ## The induced embeddings of index types -/

section IndexEmbedding

variable {U V U' V' : Type*} (f : U ↪ U') (g : V ↪ V')

/-- The embedding of matrix indices induced by `f` and `g`. -/
def pairEmb : U × V ↪ U' × V' := f.prodMap g

@[simp] theorem pairEmb_apply (p : U × V) : pairEmb f g p = (f p.1, g p.2) := rfl

/-- The embedding of vectorization indices induced by `f` and `g`, acting on all
four tensor factors at once. -/
def idxEmb : Idx U V ↪ Idx U' V' := (pairEmb f g).prodMap (pairEmb f g)

@[simp] theorem idxEmb_apply (X : Idx U V) :
    idxEmb f g X = ((f X.1.1, g X.1.2), (f X.2.1, g X.2.2)) := rfl

/-- `swU` exchanges the two `U`-slots, which the embedding treats alike. -/
theorem swU_idxEmb (X : Idx U V) : swU (idxEmb f g X) = idxEmb f g (swU X) := rfl

/-- `swV` exchanges the two `V`-slots, which the embedding treats alike. -/
theorem swV_idxEmb (X : Idx U V) : swV (idxEmb f g X) = idxEmb f g (swV X) := rfl

end IndexEmbedding

/-! ## Zero-extension of vectors and matrices -/

section Extension

variable {U V U' V' : Type*} [Fintype U] [Fintype V] [DecidableEq U'] [DecidableEq V']
  (f : U ↪ U') (g : V ↪ V')

/-- The zero-extension of a vector on `U × V` to `U' × V'`: it carries the entries
of `w` on the image of `pairEmb f g` and vanishes elsewhere. -/
noncomputable def extV (w : EuclideanSpace ℂ (U × V)) : EuclideanSpace ℂ (U' × V') :=
  WithLp.toLp 2 (fun X => ∑ p : U × V, if (f p.1, g p.2) = X then w p else 0)

theorem extV_apply (w : EuclideanSpace ℂ (U × V)) (X : U' × V') :
    extV f g w X = ∑ p : U × V, if (f p.1, g p.2) = X then w p else 0 := rfl

/-- On the image of the embedding, the zero-extension reproduces the original entries. -/
@[simp] theorem extV_apply_mk (w : EuclideanSpace ℂ (U × V)) (a : U) (b : V) :
    extV f g w (f a, g b) = w (a, b) := by
  rw [extV_apply, Finset.sum_eq_single (a, b) (fun p _ hp => if_neg ?_) (fun h => ?_)]
  · exact if_pos rfl
  · rintro hc
    exact hp (Prod.ext (f.injective (congrArg Prod.fst hc)) (g.injective (congrArg Prod.snd hc)))
  · exact absurd (Finset.mem_univ (a, b)) h

/-- The zero-extension of a matrix on `U × V` to `U' × V'`: it carries the entries
of `M` on the image of `pairEmb f g` in both indices and vanishes elsewhere. -/
noncomputable def extM (M : Matrix (U × V) (U × V) ℂ) : Matrix (U' × V') (U' × V') ℂ :=
  Matrix.of fun X Y => ∑ p : U × V, ∑ q : U × V,
    if (f p.1, g p.2) = X ∧ (f q.1, g q.2) = Y then M p q else 0

theorem extM_apply (M : Matrix (U × V) (U × V) ℂ) (X Y : U' × V') :
    extM f g M X Y = ∑ p : U × V, ∑ q : U × V,
      if (f p.1, g p.2) = X ∧ (f q.1, g q.2) = Y then M p q else 0 := rfl

/-- On the image of the embedding, the zero-extension reproduces the original entries. -/
@[simp] theorem extM_apply_mk (M : Matrix (U × V) (U × V) ℂ) (a : U) (b : V) (a' : U) (b' : V) :
    extM f g M (f a, g b) (f a', g b') = M (a, b) (a', b') := by
  rw [extM_apply, Finset.sum_eq_single (a, b) (fun p _ hp => Finset.sum_eq_zero
    fun q _ => if_neg ?_) (fun h => absurd (Finset.mem_univ (a, b)) h)]
  · rw [Finset.sum_eq_single (a', b') (fun q _ hq => if_neg ?_)
      (fun h => absurd (Finset.mem_univ (a', b')) h)]
    · exact if_pos ⟨rfl, rfl⟩
    · rintro ⟨-, hc⟩
      exact hq (Prod.ext (f.injective (congrArg Prod.fst hc)) (g.injective (congrArg Prod.snd hc)))
  · rintro ⟨hc, -⟩
    exact hp (Prod.ext (f.injective (congrArg Prod.fst hc)) (g.injective (congrArg Prod.snd hc)))

/-- The zero-extension vanishes on rows outside the image of the embedding. -/
theorem extM_apply_eq_zero_row (M : Matrix (U × V) (U × V) ℂ) {X : U' × V'}
    (hX : ∀ p : U × V, (f p.1, g p.2) ≠ X) (Y : U' × V') : extM f g M X Y = 0 := by
  rw [extM_apply]
  exact Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => if_neg fun hc => hX p hc.1

/-- The zero-extension vanishes on columns outside the image of the embedding. -/
theorem extM_apply_eq_zero_col (M : Matrix (U × V) (U × V) ℂ) (X : U' × V') {Y : U' × V'}
    (hY : ∀ q : U × V, (f q.1, g q.2) ≠ Y) : extM f g M X Y = 0 := by
  rw [extM_apply]
  exact Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => if_neg fun hc => hY q hc.2

/-- Zero-extension is additive. -/
theorem extM_add (M N : Matrix (U × V) (U × V) ℂ) :
    extM f g (M + N) = extM f g M + extM f g N := by
  ext X Y
  rw [Matrix.add_apply, extM_apply, extM_apply, extM_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  split_ifs with h
  · rfl
  · rw [add_zero]

/-- Zero-extension takes rank-one operators to rank-one operators. -/
theorem extM_rankOne (u v : EuclideanSpace ℂ (U × V)) :
    extM f g (rankOne u v) = rankOne (extV f g u) (extV f g v) := by
  have hR : ∀ (x y : EuclideanSpace ℂ (U × V)) (p q : U × V),
      rankOne x y p q = x p * conj (y q) := fun _ _ _ _ => rfl
  have hR' : ∀ (x y : EuclideanSpace ℂ (U' × V')) (X Y : U' × V'),
      rankOne x y X Y = x X * conj (y Y) := fun _ _ _ _ => rfl
  ext X Y
  rw [extM_apply, hR', extV_apply, extV_apply, map_sum]
  simp only [apply_ite (starRingEnd ℂ), map_zero]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [hR, ite_and]
  split_ifs
  · rfl
  · rw [mul_zero]
  · rw [zero_mul]
  · rw [zero_mul]

/-- The vectorization of a zero-extension agrees with that of the original matrix
along the induced index embedding. -/
theorem vec_extM_idxEmb (M : Matrix (U × V) (U × V) ℂ) (X : Idx U V) :
    vec (extM f g M) (idxEmb f g X) = vec M X := by
  obtain ⟨⟨a, b⟩, a', b'⟩ := X
  rw [vec_apply, vec_apply, idxEmb_apply]
  exact extM_apply_mk f g M a b a' b'

/-- The vectorization of a zero-extension vanishes off the image of the induced
index embedding. -/
theorem vec_extM_eq_zero (M : Matrix (U × V) (U × V) ℂ) {X : Idx U' V'}
    (hX : ∀ Y : Idx U V, idxEmb f g Y ≠ X) : vec (extM f g M) X = 0 := by
  rw [vec_apply, extM_apply]
  refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => if_neg fun hc => ?_
  refine hX (p, q) ?_
  show ((f p.1, g p.2), (f q.1, g q.2)) = X
  rw [hc.1, hc.2]

end Extension

/-! ## Preservation of the Hilbert-Schmidt norm -/

section HsNorm

variable {U V U' V' : Type*} [Fintype U] [Fintype V] [Fintype U'] [Fintype V']
  [DecidableEq U'] [DecidableEq V'] (f : U ↪ U') (g : V ↪ V')

/-- Zero-extension preserves the Hilbert-Schmidt norm: the double sum over
`U' × V'` collapses to the image of the embedding, where the entries agree. -/
theorem hsNormSq_extM (M : Matrix (U × V) (U × V) ℂ) : hsNormSq (extM f g M) = hsNormSq M := by
  have hrow : ∀ X ∈ (Finset.univ : Finset (U' × V')), X ∉ Finset.univ.map (pairEmb f g) →
      ∑ Y : U' × V', Complex.normSq (extM f g M X Y) = 0 := fun X _ hX =>
    Finset.sum_eq_zero fun Y _ => by
      rw [extM_apply_eq_zero_row f g M
        (fun p hp => hX (Finset.mem_map.2 ⟨p, Finset.mem_univ p, hp⟩)) Y, map_zero]
  have hcol : ∀ p : U × V, ∀ Y ∈ (Finset.univ : Finset (U' × V')),
      Y ∉ Finset.univ.map (pairEmb f g) →
      Complex.normSq (extM f g M (pairEmb f g p) Y) = 0 := fun p Y _ hY => by
    rw [extM_apply_eq_zero_col f g M (pairEmb f g p)
      (fun q hq => hY (Finset.mem_map.2 ⟨q, Finset.mem_univ q, hq⟩)), map_zero]
  have hinner : ∀ p : U × V, ∑ Y : U' × V', Complex.normSq (extM f g M (pairEmb f g p) Y)
      = ∑ q : U × V, Complex.normSq (M p q) := fun p => by
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map (pairEmb f g))) (hcol p),
      Finset.sum_map]
    exact Finset.sum_congr rfl fun q _ => by rw [pairEmb_apply, pairEmb_apply, extM_apply_mk]
  rw [hsNormSq, hsNormSq,
    ← Finset.sum_subset (Finset.subset_univ (Finset.univ.map (pairEmb f g))) hrow,
    Finset.sum_map]
  exact Finset.sum_congr rfl fun p _ => hinner p

end HsNorm

/-! ## Preservation of the double-antisymmetric quadratic form -/

section QuadraticForm

variable {U V U' V' : Type*} [Fintype U] [Fintype V] [Fintype U'] [Fintype V']
  [DecidableEq U] [DecidableEq V] [DecidableEq U'] [DecidableEq V']


/-- Zero-extension preserves the double-antisymmetric quadratic form.

Both `swU` and `swV` permute the `U`-slots among themselves and the `V`-slots
among themselves, so an index lies in the image of `idxEmb f g` exactly when its
image under either swap does.  Hence every term of the pointwise sum vanishes off
that image, and on it the four values are the four values of `vec M` at the
corresponding index of `Idx U V`. -/
theorem qform_Qm_vec_extM (f : U ↪ U') (g : V ↪ V') (M : Matrix (U × V) (U × V) ℂ) :
    qform Qm (vec (extM f g M)) = qform Qm (vec M) := by
  rw [qform_Qm_eq, qform_Qm_eq]
  congr 1
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map (idxEmb f g))) (fun X _ hX => ?_)]
  · rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun Y _ => ?_
    simp only [swU_idxEmb, swV_idxEmb, vec_extM_idxEmb]
  · rw [vec_extM_eq_zero f g M
      (fun Y hY => hX (Finset.mem_map.2 ⟨Y, Finset.mem_univ Y, hY⟩)), map_zero, zero_mul]

/-- **The Fu-Gao-Park bound transfers backwards along embeddings of the local
factors.**  If the bound holds on `U' ⊗ V'` and `U`, `V` embed into `U'`, `V'`,
then it holds on `U ⊗ V`: zero-extension carries a sum of two rank-one operators
to a sum of two rank-one operators without changing either side of the estimate. -/
theorem FGPBound_of_embedding (f : U ↪ U') (g : V ↪ V') (h : FGPBound U' V') :
    FGPBound U V := by
  intro u₁ v₁ u₂ v₂
  have key := h (extV f g u₁) (extV f g v₁) (extV f g u₂) (extV f g v₂)
  rwa [← extM_rankOne, ← extM_rankOne, ← extM_add, qform_Qm_vec_extM, hsNormSq_extM] at key

/-- **The square case implies the general case.**  Fu-Gao-Park's estimate on
`(ℂ^d)^{⊗4}` yields the estimate for every pair of local factors of dimension
at most `d`. -/
theorem FGPBound_of_card_le {d : ℕ} (hU : Fintype.card U ≤ d) (hV : Fintype.card V ≤ d)
    (h : FGPBound (Fin d) (Fin d)) : FGPBound U V :=
  FGPBound_of_embedding
    (Function.Embedding.nonempty_of_card_le (by simpa using hU)).some
    (Function.Embedding.nonempty_of_card_le (by simpa using hV)).some h

end QuadraticForm

section Square

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] {d : ℕ}
  (C : Matrix (U × V) (U × V) ℂ)

/-- **Theorem 1.1, from Fu–Gao–Park as published.**

The hypothesis is `FGPBound (Fin d) (Fin d)`: the double-antisymmetric
projection estimate on `(ℂ^d)^{⊗4}`, all four tensor factors the same space,
which is the form Fu–Gao–Park state.  Nothing else is assumed. -/
theorem rank_r_partial_trace_of_FGP_square
    (hU : Fintype.card U ≤ d) (hV : Fintype.card V ≤ d) (hFGP : FGPBound (Fin d) (Fin d))
    (r : ℕ) (hrank : C.rank ≤ r) :
    hsNormSq (ptraceU C) + hsNormSq (ptraceV C)
      ≤ r * hsNormSq C + (1 / r : ℝ) * Complex.normSq C.trace :=
  rank_r_partial_trace_of_FGP (FGPBound_of_card_le hU hV hFGP) C r hrank

/-- **Theorem 1.1 at the exact rank** (`eq:main-bound-exact-rank`), from
Fu–Gao–Park as published. -/
theorem rank_r_partial_trace_of_FGP_square_exact
    (hU : Fintype.card U ≤ d) (hV : Fintype.card V ≤ d) (hFGP : FGPBound (Fin d) (Fin d)) :
    hsNormSq (ptraceU C) + hsNormSq (ptraceV C)
      ≤ (C.rank : ℝ) * hsNormSq C + (1 / (C.rank : ℝ)) * Complex.normSq C.trace :=
  rank_r_partial_trace_of_FGP_exact (FGPBound_of_card_le hU hV hFGP) C

/-- **The strict form of Theorem 1.1** (`sec:proof`).  For nonzero `C` whose rank
is strictly below `r`, the rank-`r` bound is strict: the passage from the exact
rank to a larger rank parameter loses `(r-r₀)(1-1/r)‖C‖₂² > 0`. -/
theorem rank_r_partial_trace_of_FGP_square_strict
    (hU : Fintype.card U ≤ d) (hV : Fintype.card V ≤ d) (hFGP : FGPBound (Fin d) (Fin d))
    (hC : C ≠ 0) (r : ℕ) (hrank : C.rank < r) :
    hsNormSq (ptraceU C) + hsNormSq (ptraceV C)
      < r * hsNormSq C + (1 / r : ℝ) * Complex.normSq C.trace :=
  rank_r_partial_trace_of_FGP_strict (FGPBound_of_card_le hU hV hFGP) C hC r hrank

/-- **Equality in Theorem 1.1 forces `rank C = r`** (`thm:rank_r`, sharpness
paragraph).  This is why the extremizer there is built from a rank-`r`
projection. -/
theorem rank_eq_of_eq_rank_r_partial_trace_of_FGP_square
    (hU : Fintype.card U ≤ d) (hV : Fintype.card V ≤ d) (hFGP : FGPBound (Fin d) (Fin d))
    (hC : C ≠ 0) (r : ℕ) (hrank : C.rank ≤ r)
    (heq : hsNormSq (ptraceU C) + hsNormSq (ptraceV C)
      = r * hsNormSq C + (1 / r : ℝ) * Complex.normSq C.trace) :
    C.rank = r :=
  rank_eq_of_eq_rank_r_partial_trace_of_FGP (FGPBound_of_card_le hU hV hFGP) C hC r hrank heq

end Square

end RankR
