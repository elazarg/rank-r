/-
Exterior indexing: faces, position signs, and the two families of modes.

The exterior powers of `ℂ^r` enter this development only through their standard
bases, so the index set is taken to be the `m`-subsets of `Fin r` and the wedge
product is replaced by the two signs it produces.  `esign I v` is the sign with
which the vertex `v` is extracted from the wedge indexed by `I`; `placeAt u t`
puts the vector `u` on `W` at the basis coordinate labelled by the set `t`, and
is zero unless `t` labels a coordinate at all.

Two families of vectors in `W ⊗ ⋀^{k-1}ℂ^r` are built from an orthonormal family
`e₁, …, e_r` on `W`.  The incidence modes

  `η_I = k^{-1/2} ∑_{v ∈ I} esign(I, v) · ē_v ⊗ q_{I ∖ v}`,   `I` a `k`-face,

carry the hypergraph; the modes

  `δ_L = (r-k+2)^{-1/2} ∑_{j ∉ L} esign(L, j) · e_j ⊗ q_{L ∪ j}`,  `L` a `(k-2)`-face,

span the subspace that transpose symmetry protects.  Both are orthonormal: a term
of one pairs with a term of another only when the chosen vertices agree and the
two faces agree after removing that vertex, which pins the faces down.

At `k = 2` the incidence modes are the antisymmetric combinations
`(ē_i ⊗ q_j − ē_j ⊗ q_i)/√2` of the pair sector and there is one mode `δ_∅`.
-/
import RankR.Edge

namespace RankR

open Matrix Finset ComplexConjugate

/-! ## Faces and position signs -/

section Faces

variable {r : ℕ}

/-- `m`-subsets of `Fin r`, the index set of the `m`-th exterior power's standard
basis. -/
abbrev Face (r m : ℕ) := {s : Finset (Fin r) // s.card = m}

/-- The position sign `(-1)^{#\{i ∈ I : i < v\}}`, the sign with which the vertex
`v` is extracted from the wedge product indexed by `I`. -/
def esign (I : Finset (Fin r)) (v : Fin r) : ℂ := (-1) ^ (I.filter (· < v)).card

/-- Position signs are square roots of one. -/
theorem esign_mul_self (I : Finset (Fin r)) (v : Fin r) : esign I v * esign I v = 1 := by
  rw [esign, ← pow_add, ← two_mul, pow_mul]
  norm_num

/-- Position signs are real. -/
theorem conj_esign (I : Finset (Fin r)) (v : Fin r) : conj (esign I v) = esign I v := by
  rw [esign, map_pow, map_neg, map_one]

end Faces

/-! ## Placement at a face coordinate -/

section Place

variable {W : Type*} {r m : ℕ}

/-- The vector `u` on `W` placed at the basis coordinate labelled by the set `t`.
A set that is not an `m`-face labels no coordinate, and the placement is then the
zero vector, which is what makes the definition total. -/
def placeAt (u : EuclideanSpace ℂ W) (t : Finset (Fin r)) : EuclideanSpace ℂ (W × Face r m) :=
  WithLp.toLp 2 fun x => if x.2.val = t then u x.1 else 0

@[simp] theorem placeAt_apply (u : EuclideanSpace ℂ W) (t : Finset (Fin r))
    (x : W × Face r m) : placeAt u t x = if x.2.val = t then u x.1 else 0 := rfl

/-- Placing at a set of the wrong cardinality gives zero. -/
theorem placeAt_eq_zero (u : EuclideanSpace ℂ W) {t : Finset (Fin r)} (ht : t.card ≠ m) :
    (placeAt u t : EuclideanSpace ℂ (W × Face r m)) = 0 := by
  ext x
  have h : x.2.val ≠ t := fun h => ht (h ▸ x.2.2)
  simp [h]

variable [Fintype W]

/-- Two placements pair to the pairing of the placed vectors when the labels
agree, and to zero otherwise. -/
theorem inner_placeAt (u v : EuclideanSpace ℂ W) {t t' : Finset (Fin r)} (ht : t.card = m) :
    inner ℂ (placeAt u t : EuclideanSpace ℂ (W × Face r m)) (placeAt v t')
      = if t = t' then inner ℂ u v else 0 := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  by_cases htt : t = t'
  · subst htt
    rw [if_pos rfl, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_eq_single (⟨t, ht⟩ : Face r m)]
    · simp
    · intro b _ hb
      have hbt : b.val ≠ t := fun h => hb (Subtype.ext h)
      simp [hbt]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [if_neg htt]
    refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun J _ => ?_
    by_cases h1 : J.val = t
    · have h2 : J.val ≠ t' := fun h => htt (h1 ▸ h)
      simp [h2]
    · simp [h1]

end Place

/-! ## Operators acting trivially on the face factor -/

section PlaceT

variable {W T : Type*} [DecidableEq T]

/-- `A ⊗ I_T`, for `A` on `W`, placed on `W ⊗ T` for an arbitrary ancilla `T`. -/
def placeT (A : Matrix W W ℂ) : Matrix (W × T) (W × T) ℂ :=
  Matrix.of fun x y => if x.2 = y.2 then A x.1 y.1 else 0

@[simp] theorem placeT_apply (A : Matrix W W ℂ) (x y : W × T) :
    placeT A x y = if x.2 = y.2 then A x.1 y.1 else 0 := rfl

/-- Placing an operator on the ancilla is additive. -/
theorem placeT_sum {ι : Type*} [Fintype ι] (A : ι → Matrix W W ℂ) :
    placeT (T := T) (∑ i, A i) = ∑ i, placeT (T := T) (A i) := by
  ext x y
  simp only [placeT_apply, Matrix.sum_apply]
  split_ifs with h
  · rfl
  · exact Finset.sum_const_zero.symm

/-- Placing an operator on the ancilla is homogeneous. -/
theorem placeT_smul (c : ℂ) (A : Matrix W W ℂ) :
    placeT (T := T) (c • A) = c • placeT (T := T) A := by
  ext x y
  simp only [placeT_apply, Matrix.smul_apply, smul_eq_mul, mul_ite, mul_zero]

variable {r m : ℕ} [Fintype W]

/-- An operator acting trivially on the face factor preserves the label of a
placed vector. -/
theorem mulVecE_placeT_placeAt (N : Matrix W W ℂ) (u : EuclideanSpace ℂ W)
    (t : Finset (Fin r)) :
    mulVecE (placeT (T := Face r m) N) (placeAt u t) = placeAt (mulVecE N u) t := by
  ext x
  rw [mulVecE_apply, placeAt_apply, mulVecE_apply, Fintype.sum_prod_type]
  have h : ∀ q : W, (∑ J : Face r m, placeT (T := Face r m) N x (q, J) * placeAt u t (q, J))
      = if x.2.val = t then N x.1 q * u q else 0 := fun q => by
    have h' : ∀ J : Face r m, placeT (T := Face r m) N x (q, J) * placeAt u t (q, J)
        = if J = x.2 then (if x.2.val = t then N x.1 q * u q else 0) else 0 := fun J => by
      by_cases hJ : J = x.2
      · rw [if_pos hJ, hJ]
        by_cases hx : x.2.val = t <;> simp [hx]
      · simp [hJ, Ne.symm hJ]
    rw [Finset.sum_congr rfl fun J _ => h' J, Finset.sum_ite_eq']
    simp
  rw [Finset.sum_congr rfl fun q _ => h q]
  by_cases hx : x.2.val = t <;> simp [hx]

end PlaceT

/-! ## The incidence modes -/

section Eta

variable {W : Type*} [Fintype W] {r k : ℕ}

/-- The exterior incidence mode of the `k`-face `I`: each vertex of `I` is
extracted with its position sign and the conjugate `ē_v` is placed at the
`(k-1)`-face `I ∖ v`.

The sum runs over all of `Fin r`; a vertex outside `I` leaves `I` unchanged, and
a set of cardinality `k` labels no `(k-1)`-face, so those terms vanish. -/
noncomputable def etaMode (e : Fin r → EuclideanSpace ℂ W) (I : Face r k) :
    EuclideanSpace ℂ (W × Face r (k - 1)) :=
  ((Real.sqrt k : ℝ) : ℂ)⁻¹ • ∑ v : Fin r, esign I.val v • placeAt (ebar e v) (I.val.erase v)

/-- A term of one incidence mode pairs with a term of another only when the two
extracted vertices agree and lie in the first face; the two faces then agree
after removing that vertex, which forces them to be equal. -/
theorem inner_placeAt_erase {e : Fin r → EuclideanSpace ℂ W} (he : Orthonormal ℂ e)
    (hk : 1 ≤ k) (I I' : Face r k) (v v' : Fin r) :
    inner ℂ (placeAt (ebar e v) (I.val.erase v) : EuclideanSpace ℂ (W × Face r (k - 1)))
        (placeAt (ebar e v') (I'.val.erase v'))
      = if v = v' ∧ v ∈ I.val ∧ I = I' then 1 else 0 := by
  by_cases hv : v ∈ I.val
  · have hc : (I.val.erase v).card = k - 1 := by rw [Finset.card_erase_of_mem hv, I.2]
    rw [inner_placeAt _ _ hc, orthonormal_iff_ite.mp (orthonormal_ebar he) v v']
    by_cases hvv : v = v'
    · subst hvv
      rw [if_pos rfl]
      have hiff : I.val.erase v = I'.val.erase v ↔ I = I' := by
        constructor
        · intro h
          have hv' : v ∈ I'.val := by
            by_contra hv'
            rw [Finset.erase_eq_of_notMem hv'] at h
            have hcc := congrArg Finset.card h
            rw [hc, I'.2] at hcc
            omega
          refine Subtype.ext ?_
          rw [← Finset.insert_erase hv, ← Finset.insert_erase hv', h]
        · intro h; rw [h]
      by_cases hII : I = I'
      · rw [if_pos (hiff.mpr hII), if_pos ⟨rfl, hv, hII⟩]
      · rw [if_neg (fun h => hII (hiff.mp h)), if_neg (fun h => hII h.2.2)]
    · rw [if_neg hvv, ite_self, if_neg (fun h => hvv h.1)]
  · have hc : (I.val.erase v).card ≠ k - 1 := by
      rw [Finset.erase_eq_of_notMem hv, I.2]
      omega
    rw [placeAt_eq_zero _ hc, inner_zero_left, if_neg (fun h => hv h.2.1)]

/-- The reciprocal of `√n`, squared, is the reciprocal of `n`. -/
theorem inv_sqrt_mul_inv_sqrt (n : ℕ) :
    conj ((Real.sqrt n : ℝ) : ℂ)⁻¹ * ((Real.sqrt n : ℝ) : ℂ)⁻¹ = ((n : ℝ) : ℂ)⁻¹ := by
  have h1 : conj ((Real.sqrt n : ℝ) : ℂ)⁻¹ = ((Real.sqrt n : ℝ) : ℂ)⁻¹ := by
    rw [map_inv₀, Complex.conj_ofReal]
  rw [h1, ← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Complex.ofReal_inv, ← mul_inv,
    Real.mul_self_sqrt (Nat.cast_nonneg n)]

/-- The incidence modes are orthonormal. -/
theorem inner_etaMode {e : Fin r → EuclideanSpace ℂ W} (he : Orthonormal ℂ e) (hk : 1 ≤ k)
    (I I' : Face r k) : inner ℂ (etaMode e I) (etaMode e I') = if I = I' then 1 else 0 := by
  have hkR : ((k : ℝ) : ℂ) ≠ 0 := by
    have : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    exact_mod_cast this
  rw [etaMode, etaMode, inner_smul_left, inner_smul_right, sum_inner]
  have hv : ∀ v : Fin r,
      inner ℂ (esign I.val v • placeAt (ebar e v) (I.val.erase v)
          : EuclideanSpace ℂ (W × Face r (k - 1)))
        (∑ v' : Fin r, esign I'.val v' • placeAt (ebar e v') (I'.val.erase v'))
      = if v ∈ I.val ∧ I = I' then 1 else 0 := fun v => by
    rw [inner_smul_left, inner_sum, conj_esign]
    have hv' : ∀ v' : Fin r,
        inner ℂ (placeAt (ebar e v) (I.val.erase v) : EuclideanSpace ℂ (W × Face r (k - 1)))
            (esign I'.val v' • placeAt (ebar e v') (I'.val.erase v'))
          = if v' = v then esign I.val v * (if v ∈ I.val ∧ I = I' then 1 else 0) else 0 :=
      fun v' => by
        rw [inner_smul_right, inner_placeAt_erase he hk I I' v v']
        by_cases hvv : v = v'
        · subst hvv
          by_cases hcond : v ∈ I.val ∧ I = I'
          · rw [if_pos ⟨rfl, hcond.1, hcond.2⟩, if_pos rfl, if_pos hcond, mul_one, mul_one,
              hcond.2]
          · rw [if_neg (fun h => hcond ⟨h.2.1, h.2.2⟩), if_pos rfl, if_neg hcond,
              mul_zero, mul_zero]
        · rw [if_neg (fun h => hvv h.1), if_neg (Ne.symm hvv), mul_zero]
    rw [Finset.sum_congr rfl fun v' _ => hv' v', Finset.sum_ite_eq' Finset.univ v,
      if_pos (Finset.mem_univ v), ← mul_assoc, esign_mul_self, one_mul]
  rw [Finset.sum_congr rfl fun v _ => hv v]
  by_cases hII : I = I'
  · subst hII
    have hcount : ∑ v : Fin r, (if v ∈ I.val ∧ I = I then (1 : ℂ) else 0) = ((k : ℝ) : ℂ) := by
      have h : ∀ v : Fin r, (if v ∈ I.val ∧ I = I then (1 : ℂ) else 0)
          = if v ∈ I.val then 1 else 0 := fun v => by simp
      rw [Finset.sum_congr rfl fun v _ => h v, Finset.sum_ite_mem, Finset.univ_inter,
        Finset.sum_const, I.2]
      simp
    rw [hcount, if_pos rfl, ← mul_assoc, inv_sqrt_mul_inv_sqrt, inv_mul_cancel₀ hkR]
  · have h : ∀ v : Fin r, (if v ∈ I.val ∧ I = I' then (1 : ℂ) else 0) = 0 :=
      fun v => if_neg (fun h => hII h.2)
    rw [Finset.sum_congr rfl fun v _ => h v, Finset.sum_const_zero, mul_zero, mul_zero,
      if_neg hII]

/-- **The incidence modes form an orthonormal family.** -/
theorem orthonormal_etaMode {e : Fin r → EuclideanSpace ℂ W} (he : Orthonormal ℂ e)
    (hk : 1 ≤ k) : Orthonormal ℂ (etaMode e : Face r k → EuclideanSpace ℂ (W × Face r (k - 1))) :=
  orthonormal_iff_ite.mpr fun I I' => inner_etaMode he hk I I'

end Eta

/-! ## The protected modes -/

section Delta

variable {W : Type*} [Fintype W] {r k : ℕ}

/-- The mode attached to the `(k-2)`-face `L`: each vertex outside `L` is adjoined
with its position sign relative to `L`, and `e_j` is placed at the `(k-1)`-face
`L ∪ j`.

The sum runs over all of `Fin r`; a vertex already in `L` leaves `L` unchanged,
and a set of cardinality `k-2` labels no `(k-1)`-face, so those terms vanish. -/
noncomputable def deltaMode (e : Fin r → EuclideanSpace ℂ W) (L : Face r (k - 2)) :
    EuclideanSpace ℂ (W × Face r (k - 1)) :=
  ((Real.sqrt ((r - k + 2 : ℕ) : ℝ) : ℝ) : ℂ)⁻¹ •
    ∑ j : Fin r, esign L.val j • placeAt (e j) (insert j L.val)

/-- A term of one protected mode pairs with a term of another only when the two
adjoined vertices agree and lie outside the first face; the two faces then agree
after adjoining that vertex, which forces them to be equal. -/
theorem inner_placeAt_insert {e : Fin r → EuclideanSpace ℂ W} (he : Orthonormal ℂ e)
    (hk : 2 ≤ k) (L L' : Face r (k - 2)) (j j' : Fin r) :
    inner ℂ (placeAt (e j) (insert j L.val) : EuclideanSpace ℂ (W × Face r (k - 1)))
        (placeAt (e j') (insert j' L'.val))
      = if j = j' ∧ j ∉ L.val ∧ L = L' then 1 else 0 := by
  by_cases hj : j ∈ L.val
  · have hc : (insert j L.val).card ≠ k - 1 := by
      rw [Finset.insert_eq_self.mpr hj, L.2]
      omega
    rw [placeAt_eq_zero _ hc, inner_zero_left, if_neg (fun h => h.2.1 hj)]
  · have hc : (insert j L.val).card = k - 1 := by
      rw [Finset.card_insert_of_notMem hj, L.2]
      omega
    rw [inner_placeAt _ _ hc, orthonormal_iff_ite.mp he j j']
    by_cases hjj : j = j'
    · subst hjj
      rw [if_pos rfl]
      have hiff : insert j L.val = insert j L'.val ↔ L = L' := by
        constructor
        · intro h
          have hj' : j ∉ L'.val := by
            intro hj'
            rw [Finset.insert_eq_self.mpr hj'] at h
            have hcc := congrArg Finset.card h
            rw [hc, L'.2] at hcc
            omega
          refine Subtype.ext ?_
          rw [← Finset.erase_insert hj, ← Finset.erase_insert hj', h]
        · intro h; rw [h]
      by_cases hLL : L = L'
      · rw [if_pos (hiff.mpr hLL), if_pos ⟨rfl, hj, hLL⟩]
      · rw [if_neg (fun h => hLL (hiff.mp h)), if_neg (fun h => hLL h.2.2)]
    · rw [if_neg hjj, ite_self, if_neg (fun h => hjj h.1)]

/-- The protected modes are orthonormal. -/
theorem inner_deltaMode {e : Fin r → EuclideanSpace ℂ W} (he : Orthonormal ℂ e)
    (hk : 2 ≤ k) (hkr : k ≤ r) (L L' : Face r (k - 2)) :
    inner ℂ (deltaMode e L) (deltaMode (k := k) e L') = if L = L' then 1 else 0 := by
  have hN : 1 ≤ r - k + 2 := by omega
  have hNR : (((r - k + 2 : ℕ) : ℝ) : ℂ) ≠ 0 := by
    have : ((r - k + 2 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    exact_mod_cast this
  rw [deltaMode, deltaMode, inner_smul_left, inner_smul_right, sum_inner]
  have hj : ∀ j : Fin r,
      inner ℂ (esign L.val j • placeAt (e j) (insert j L.val)
          : EuclideanSpace ℂ (W × Face r (k - 1)))
        (∑ j' : Fin r, esign L'.val j' • placeAt (e j') (insert j' L'.val))
      = if j ∉ L.val ∧ L = L' then 1 else 0 := fun j => by
    rw [inner_smul_left, inner_sum, conj_esign]
    have hj' : ∀ j' : Fin r,
        inner ℂ (placeAt (e j) (insert j L.val) : EuclideanSpace ℂ (W × Face r (k - 1)))
            (esign L'.val j' • placeAt (e j') (insert j' L'.val))
          = if j' = j then esign L.val j * (if j ∉ L.val ∧ L = L' then 1 else 0) else 0 :=
      fun j' => by
        rw [inner_smul_right, inner_placeAt_insert he hk L L' j j']
        by_cases hjj : j = j'
        · subst hjj
          by_cases hcond : j ∉ L.val ∧ L = L'
          · rw [if_pos ⟨rfl, hcond.1, hcond.2⟩, if_pos rfl, if_pos hcond, mul_one, mul_one,
              hcond.2]
          · rw [if_neg (fun h => hcond ⟨h.2.1, h.2.2⟩), if_pos rfl, if_neg hcond,
              mul_zero, mul_zero]
        · rw [if_neg (fun h => hjj h.1), if_neg (Ne.symm hjj), mul_zero]
    rw [Finset.sum_congr rfl fun j' _ => hj' j', Finset.sum_ite_eq' Finset.univ j,
      if_pos (Finset.mem_univ j), ← mul_assoc, esign_mul_self, one_mul]
  rw [Finset.sum_congr rfl fun j _ => hj j]
  by_cases hLL : L = L'
  · subst hLL
    have hcount : ∑ j : Fin r, (if j ∉ L.val ∧ L = L then (1 : ℂ) else 0)
        = (((r - k + 2 : ℕ) : ℝ) : ℂ) := by
      have h : ∀ j : Fin r, (if j ∉ L.val ∧ L = L then (1 : ℂ) else 0)
          = if j ∈ L.valᶜ then 1 else 0 := fun j => by simp
      rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_ite_mem, Finset.univ_inter,
        Finset.sum_const, Finset.card_compl, L.2, Fintype.card_fin]
      have hcard : r - (k - 2) = r - k + 2 := by omega
      rw [hcard]
      simp
    rw [hcount, if_pos rfl, ← mul_assoc, inv_sqrt_mul_inv_sqrt, inv_mul_cancel₀ hNR]
  · have h : ∀ j : Fin r, (if j ∉ L.val ∧ L = L' then (1 : ℂ) else 0) = 0 :=
      fun j => if_neg (fun h => hLL h.2)
    rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_const_zero, mul_zero, mul_zero,
      if_neg hLL]

/-- **The protected modes form an orthonormal family**, one for each
`(k-2)`-face. -/
theorem orthonormal_deltaMode {e : Fin r → EuclideanSpace ℂ W} (he : Orthonormal ℂ e)
    (hk : 2 ≤ k) (hkr : k ≤ r) :
    Orthonormal ℂ (deltaMode (k := k) e : Face r (k - 2) → EuclideanSpace ℂ (W × Face r (k - 1))) :=
  orthonormal_iff_ite.mpr fun L L' => inner_deltaMode he hk hkr L L'

end Delta

end RankR
