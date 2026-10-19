/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.LocalLength.KoszulDimensionBound

/-!
# Consumers of the local finite-list dimension bound

The bound applies to actual module quotients, including square-ideal
thickenings and repeated or zero equations. The empty-list consumer recovers
zero-dimensional support. None of the tests assumes scalar regularity.
-/

@[expose] public section

universe u v

namespace MotivicTest.KoszulDimensionBound

open Module

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- The two-equation bound applies to the actual square-ideal thickening. -/
theorem squareThickening (J : Ideal R) (a b : R)
    (ha : a ∈ IsLocalRing.maximalIdeal R) (hb : b ∈ IsLocalRing.maximalIdeal R)
    [IsArtinianRing (R ⧸ (Ideal.ofList [a, b] ⊔ J ^ 2))] :
    Module.supportDim R (R ⧸ J ^ 2) ≤ 2 := by
  exact koszulDimension_quotient_le_length (J ^ 2) [a, b]
    (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> assumption)

/-- A repeated equation and a zero equation satisfy the same arbitrary-list
bound; the finite quotient hypothesis is sufficient without a regular list. -/
theorem repeatedZero (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (a : R) (ha : a ∈ IsLocalRing.maximalIdeal R)
    [IsArtinianRing (R ⧸ (Ideal.ofList [a, a, 0] ⊔ Module.annihilator R M))] :
    Module.supportDim R M ≤ 3 := by
  exact koszulDimension_le_length_of_artinian_support_quotient M [a, a, 0]
    (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact ha
        · exact ha
        · exact (IsLocalRing.maximalIdeal R).zero_mem)

/-- With no equations, an Artinian coefficient-support quotient already has
support dimension at most zero. -/
theorem emptyList (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [IsArtinianRing (R ⧸ Module.annihilator R M)] :
    Module.supportDim R M ≤ 0 := by
  have : IsArtinianRing (R ⧸ (Ideal.ofList ([] : List R) ⊔ Module.annihilator R M)) := by
    rw [Ideal.ofList_nil, bot_sup_eq]
    infer_instance
  exact koszulDimension_le_length_of_artinian_support_quotient M [] (by simp)

omit [IsLocalRing R] in
/-- The same hypotheses give actual finite module length of the equation
quotient, rather than merely a numerical dimension bound. -/
theorem actualQuotientFiniteLength (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] (s : List R)
    [IsArtinianRing (R ⧸ (Ideal.ofList s ⊔ Module.annihilator R M))] :
    Module.length R (M ⧸ (Ideal.ofList s • ⊤ : Submodule R M)) ≠ ⊤ :=
  koszulDimension_quotient_length_ne_top M s

end MotivicTest.KoszulDimensionBound
