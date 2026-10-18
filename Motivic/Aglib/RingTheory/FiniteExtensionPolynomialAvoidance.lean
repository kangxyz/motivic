/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.FieldTheory.Finite.Polynomial

/-!
# Polynomial avoidance in sufficiently large finite extensions

The degree bound is explicit. Finite extensions remain finite; evaluation is
injective only on the bounded-degree subspace, not on the entire polynomial ring.
-/

@[expose] public noncomputable section

namespace MvPolynomial

universe u v w

/-- A nonzero polynomial has a nonzero value over a finite extension whose
cardinality exceeds its total degree. -/
theorem exists_eval₂_ne_zero_of_totalDegree_lt_card
    {k : Type u} [Field k] {L : Type v} [Field L] [Finite L]
    [Algebra k L] {σ : Type w} [Finite σ]
    (q : MvPolynomial σ k) (hq : q ≠ 0)
    (hcard : q.totalDegree < Nat.card L) :
    ∃ c : σ → L, eval₂ (algebraMap k L) c q ≠ 0 := by
  classical
  let := Fintype.ofFinite L
  let := Fintype.ofFinite σ
  let e : σ ≃ ULift.{v} (Fin (Fintype.card σ)) :=
    (Fintype.equivFin σ).trans Equiv.ulift.symm
  let r := rename e (map (algebraMap k L) q)
  have hmap : map (algebraMap k L) q ≠ 0 :=
    fun h => hq ((map_injective _ (algebraMap k L).injective) (by simpa using h))
  have hr : r ≠ 0 := fun h => hmap
    ((rename_injective e e.injective) (by simpa [r] using h))
  have hdeg : r.totalDegree ≤ q.totalDegree :=
    (totalDegree_rename_le e _).trans
      (Finset.sup_mono (support_map_subset (algebraMap k L) q))
  by_contra! h
  apply hr
  apply eq_zero_of_eval_eq_zero (ULift.{v} (Fin (Fintype.card σ))) L r
  · intro c
    simpa only [r, eval_rename, ← eval₂_eq_eval_map] using h (c ∘ e)
  · apply (mem_restrictDegree _ _ _).mpr
    intro s hs i
    have hi := ((monomial_le_degreeOf i hs).trans (degreeOf_le_totalDegree r i)).trans hdeg
    have hc : q.totalDegree < Fintype.card L := by
      simpa only [Fintype.card_eq_nat_card] using hcard
    exact hi.trans (Nat.le_sub_one_of_lt hc)

/-- Every sufficiently large positive degree works, rather than just one
unspecified finite extension. This permits later choices of coprime degrees. -/
theorem exists_eval₂_ne_zero_finiteExtension
    (k : Type u) [Field k] [Finite k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {σ : Type w} [Finite σ] (q : MvPolynomial σ k) (hq : q ≠ 0)
    (n : ℕ) [NeZero n] (hn : q.totalDegree < n) :
    ∃ c : σ → FiniteField.Extension k p n,
      eval₂ (algebraMap k (FiniteField.Extension k p n)) c q ≠ 0 := by
  apply exists_eval₂_ne_zero_of_totalDegree_lt_card q hq
  rw [FiniteField.natCard_extension]
  exact hn.trans (Nat.lt_pow_self Finite.one_lt_card)

end MvPolynomial
