/-
Constant diagonals under unitary similarity.

The finite-dimensional induction is separated from the numerical-range input:
one trace-average diagonal entry at each positive dimension produces a full
constant diagonal.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace RankR

open Matrix Finset ComplexConjugate

/-- A matrix has a constant diagonal up to unitary similarity. -/
def HasConstantDiagonal {q : ℕ} (A : Matrix (Fin q) (Fin q) ℂ) : Prop :=
  ∃ U : Matrix (Fin q) (Fin q) ℂ,
    U ∈ Matrix.unitaryGroup (Fin q) ℂ
      ∧ ∀ i, (Uᴴ * A * U) i i = A.trace / (q : ℂ)

/-- The Parker--Fillmore property in a fixed dimension. -/
def HasConstantDiagonals (q : ℕ) : Prop :=
  ∀ A : Matrix (Fin q) (Fin q) ℂ, HasConstantDiagonal A

/-- A positive dimension has the trace-entry property if every matrix has a
unitary conjugate whose first diagonal entry is the trace average. -/
def HasTraceEntry (q : ℕ) : Prop :=
  ∀ A : Matrix (Fin q.succ) (Fin q.succ) ℂ,
    ∃ U : Matrix (Fin q.succ) (Fin q.succ) ℂ,
      U ∈ Matrix.unitaryGroup (Fin q.succ) ℂ
        ∧ (Uᴴ * A * U) 0 0 = A.trace / (q.succ : ℂ)

/-- Put a scalar in the first block and a matrix in the successor block. -/
def succBlock {q : ℕ} (a : ℂ) (V : Matrix (Fin q) (Fin q) ℂ) :
    Matrix (Fin q.succ) (Fin q.succ) ℂ :=
  fun i => Fin.cases
    (fun j => Fin.cases a (fun _ => 0) j)
    (fun i j => Fin.cases 0 (fun j => V i j) j)
    i

@[simp]
theorem succBlock_zero_zero {q : ℕ} (a : ℂ) (V : Matrix (Fin q) (Fin q) ℂ) :
    succBlock a V 0 0 = a :=
  rfl

@[simp]
theorem succBlock_zero_succ {q : ℕ} (a : ℂ) (V : Matrix (Fin q) (Fin q) ℂ)
    (j : Fin q) :
    succBlock a V 0 j.succ = 0 :=
  rfl

@[simp]
theorem succBlock_succ_zero {q : ℕ} (a : ℂ) (V : Matrix (Fin q) (Fin q) ℂ)
    (i : Fin q) :
    succBlock a V i.succ 0 = 0 :=
  rfl

@[simp]
theorem succBlock_succ_succ {q : ℕ} (a : ℂ) (V : Matrix (Fin q) (Fin q) ℂ)
    (i j : Fin q) :
    succBlock a V i.succ j.succ = V i j :=
  rfl

@[simp]
theorem succBlock_conjTranspose {q : ℕ} (a : ℂ)
    (V : Matrix (Fin q) (Fin q) ℂ) :
    (succBlock a V)ᴴ = succBlock (conj a) Vᴴ := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j <;>
      simp [Matrix.conjTranspose_apply]

@[simp]
theorem succBlock_mul {q : ℕ} (a b : ℂ)
    (V W : Matrix (Fin q) (Fin q) ℂ) :
    succBlock a V * succBlock b W = succBlock (a * b) (V * W) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp [Matrix.mul_apply, Fin.sum_univ_succ]
    · simp [Matrix.mul_apply, Fin.sum_univ_succ]
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp [Matrix.mul_apply, Fin.sum_univ_succ]
    · simp [Matrix.mul_apply, Fin.sum_univ_succ]

@[simp]
theorem succBlock_one {q : ℕ} :
    succBlock 1 (1 : Matrix (Fin q) (Fin q) ℂ) = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · simp [(Fin.succ_ne_zero j).symm]
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp [Fin.succ_ne_zero i]
    · simp [Matrix.one_apply]

/-- Adjoining a one-dimensional identity block preserves unitarity. -/
theorem succBlock_mem_unitary {q : ℕ} {V : Matrix (Fin q) (Fin q) ℂ}
    (hV : V ∈ Matrix.unitaryGroup (Fin q) ℂ) :
    succBlock 1 V ∈ Matrix.unitaryGroup (Fin q.succ) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    succBlock_conjTranspose, map_one, succBlock_mul]
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hV
  rw [hV]
  simpa only [one_mul] using (succBlock_one (q := q))

/-- The scalar corner is unchanged by conjugation with a successor block. -/
@[simp]
theorem succBlock_conjugate_zero_zero {q : ℕ}
    (V : Matrix (Fin q) (Fin q) ℂ)
    (B : Matrix (Fin q.succ) (Fin q.succ) ℂ) :
    ((succBlock 1 V)ᴴ * B * succBlock 1 V) 0 0 = B 0 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_succ]

/-- The successor principal submatrix is conjugated by the successor block. -/
theorem succBlock_conjugate_succ_succ {q : ℕ}
    (V : Matrix (Fin q) (Fin q) ℂ)
    (B : Matrix (Fin q.succ) (Fin q.succ) ℂ) (i j : Fin q) :
    ((succBlock 1 V)ᴴ * B * succBlock 1 V) i.succ j.succ =
      (Vᴴ * B.submatrix Fin.succ Fin.succ * V) i j := by
  simp [Matrix.mul_apply, Fin.sum_univ_succ]

/-- Unitary conjugation preserves the trace. -/
theorem trace_unitary_conjugate {q : ℕ}
    {U : Matrix (Fin q) (Fin q) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin q) ℂ)
    (A : Matrix (Fin q) (Fin q) ℂ) :
    (Uᴴ * A * U).trace = A.trace := by
  rw [Matrix.trace_mul_cycle]
  have hrow : U * Uᴴ = (1 : Matrix (Fin q) (Fin q) ℂ) := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff.mp hU)
  rw [hrow, Matrix.one_mul]

/-- The constant-diagonal property in dimension zero. -/
theorem hasConstantDiagonals_zero : HasConstantDiagonals 0 := by
  intro A
  refine ⟨1, by simp, ?_⟩
  intro i
  exact Fin.elim0 i

/-- The constant-diagonal property in dimension one. -/
theorem hasConstantDiagonals_one : HasConstantDiagonals 1 := by
  intro A
  refine ⟨1, by simp, ?_⟩
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp [Matrix.trace]

/-- A trace-average first entry in every positive dimension yields the full
Parker--Fillmore constant-diagonal property by compression and induction. -/
theorem hasConstantDiagonals_of_traceEntry
    (hentry : ∀ q, HasTraceEntry q) :
    ∀ q, HasConstantDiagonals q := by
  intro q
  induction q with
  | zero => exact hasConstantDiagonals_zero
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        exact hasConstantDiagonals_one
      · intro A
        obtain ⟨U, hU, hfirst⟩ := hentry n A
        let B := Uᴴ * A * U
        let C := B.submatrix Fin.succ Fin.succ
        have htraceB : B.trace = A.trace := by
          exact trace_unitary_conjugate hU A
        have hfirstB : B 0 0 = A.trace / (n.succ : ℂ) :=
          hfirst
        have hsplit : B 0 0 + C.trace = B.trace := by
          simpa only [C] using Matrix.trace_submatrix_succ B
        have htraceC :
            C.trace = (n : ℂ) * (A.trace / (n.succ : ℂ)) := by
          have hdiff :
              C.trace = A.trace - A.trace / (n.succ : ℂ) := by
            rw [hfirstB, htraceB] at hsplit
            exact eq_sub_of_add_eq (by simpa only [add_comm] using hsplit)
          rw [hdiff]
          have hsucc : (n.succ : ℂ) ≠ 0 := by
            exact_mod_cast Nat.succ_ne_zero n
          field_simp
          rw [Nat.cast_succ]
          ring
        have hratio : C.trace / (n : ℂ) = A.trace / (n.succ : ℂ) := by
          have hncast : (n : ℂ) ≠ 0 := by
            exact_mod_cast hn
          apply (div_eq_iff hncast).2
          simpa only [mul_comm] using htraceC
        obtain ⟨V, hV, hdiagV⟩ := ih C
        let Q := succBlock 1 V
        let W := U * Q
        have hQ : Q ∈ Matrix.unitaryGroup (Fin n.succ) ℂ :=
          succBlock_mem_unitary hV
        have hW : W ∈ Matrix.unitaryGroup (Fin n.succ) ℂ :=
          (Matrix.unitaryGroup (Fin n.succ) ℂ).mul_mem hU hQ
        have hconj : Wᴴ * A * W = Qᴴ * B * Q := by
          simp only [W, Q, B, Matrix.conjTranspose_mul, Matrix.mul_assoc]
        refine ⟨W, hW, ?_⟩
        intro i
        refine Fin.cases ?_ (fun i => ?_) i
        · rw [hconj]
          simpa only [Q, succBlock_conjugate_zero_zero] using hfirstB
        · rw [hconj, succBlock_conjugate_succ_succ]
          exact (hdiagV i).trans hratio

end RankR
