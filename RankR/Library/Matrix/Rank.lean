/-
Rank-sensitive finite-matrix infrastructure.

This module exposes the exact-rank range factorization and the trace-rank
bound.
-/
import RankR.Library.Matrix.RankFactorization
import Mathlib.LinearAlgebra.Matrix.Rank

namespace RankR

open Matrix Finset ComplexConjugate

section Rank

/-- Transposition preserves a rank upper bound. -/
theorem rank_transpose_le {W : Type*} [Fintype W]
    {A : Matrix W W ℂ} {k : ℕ}
    (h : A.rank ≤ k) :
    Aᵀ.rank ≤ k := by
  rwa [Matrix.rank_transpose]

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The factorization's index type has the manuscript's `r₀ = rank C`. -/
theorem finrank_range_toEuclideanLin (C : Matrix W W ℂ) :
    Module.finrank ℂ (LinearMap.range (Matrix.toEuclideanLin C)) = C.rank := by
  rw [Matrix.rank_eq_finrank_range_toLin C (EuclideanSpace.basisFun W ℂ).toBasis
    (EuclideanSpace.basisFun W ℂ).toBasis]
  rfl

omit [DecidableEq W] in
/-- The range factorization, re-indexed by `C.rank`.

`Matrix.rank` decides no equality, so neither does this statement: the
`DecidableEq` of `exists_rankFactor` is an artifact of `Matrix.toEuclideanLin`,
which appears only in the proof.  Everything downstream of this lemma is free
of it. -/
theorem exists_rankFactor_rank (C : Matrix W W ℂ) :
    ∃ e d : Fin C.rank → EuclideanSpace ℂ W, Orthonormal ℂ e ∧ C = rankFactor e d := by
  classical
  exact (finrank_range_toEuclideanLin C) ▸ exists_rankFactor C

omit [DecidableEq W] in
/-- Rank `0` means the empty range factorization, hence the zero matrix. -/
theorem eq_zero_of_rank_eq_zero {C : Matrix W W ℂ} (h : C.rank = 0) : C = 0 := by
  obtain ⟨e, d, _, hC⟩ := exists_rankFactor_rank C
  have huniv : (Finset.univ : Finset (Fin C.rank)) = ∅ := by
    rw [← Finset.card_eq_zero, Finset.card_univ, Fintype.card_fin]
    exact h
  rw [hC]
  ext p q
  simp [rankFactor_apply, huniv]

omit [DecidableEq W] in
theorem rank_pos_of_ne_zero {C : Matrix W W ℂ} (h : C ≠ 0) : 0 < C.rank :=
  Nat.pos_of_ne_zero fun h0 => h (eq_zero_of_rank_eq_zero h0)

omit [DecidableEq W] in
/-- The trace-rank bound `|Tr C|² ≤ (rank C)‖C‖₂²`, stated for `C` itself.
This is `normSq_trace_le` transported along the range factorization. -/
theorem normSq_trace_le_rank (C : Matrix W W ℂ) :
    Complex.normSq C.trace ≤ (C.rank : ℝ) * hsNormSq C := by
  obtain ⟨e, d, he, hC⟩ := exists_rankFactor_rank C
  have h := normSq_trace_le e d he
  rwa [← hC] at h

end Rank

end RankR
