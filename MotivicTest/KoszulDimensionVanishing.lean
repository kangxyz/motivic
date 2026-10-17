/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulDimensionVanishing

/-!
# Consumers of full Koszul dimension vanishing

These consumers apply the completed prime-filtration induction to arbitrary
finite coefficients, the empty list, zero coefficients, and a dependent pair
of equal equations. The dependent-pair test only requires the quotient by
one equation to have Artinian support, so the coefficient module can have
positive dimension and need not have finite length.
-/

@[expose] public section

universe u

open CategoryTheory Motivic.Koszul Motivic.LengthEuler

namespace MotivicTest.KoszulDimensionVanishing

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- Genuine arbitrary-module dimension vanishing, with no prime-quotient or
regular-sequence hypothesis. -/
theorem arbitraryCoefficients (M : ModuleCat R) [Module.Finite R M]
    (s : List R) (hs : ∀ a ∈ s, a ∈ IsLocalRing.maximalIdeal R)
    (hd : Module.supportDim R M < s.length)
    [IsArtinianRing (R ⧸ (Ideal.ofList s ⊔ Module.annihilator R M))] :
    chainEuler (coefficientComplex M s) (finiteHomology_of_artinian_support_quotient M s) = 0 :=
  koszulDimension_chainEuler_zero M s hs hd

/-- The induction base uses the actual empty coefficient complex. -/
theorem emptyList (M : ModuleCat R) [Module.Finite R M]
    (hd : Module.supportDim R M < 0)
    [IsArtinianRing (R ⧸ (Ideal.ofList [] ⊔ Module.annihilator R M))] :
    chainEuler (coefficientComplex M []) (finiteHomology_of_artinian_support_quotient M []) = 0 :=
  koszulDimension_chainEuler_zero M [] (by simp) hd

/-- Zero coefficients satisfy the dimension-defect input for every list. -/
theorem zeroCoefficients (M : ModuleCat R) [Module.Finite R M] [Subsingleton M]
    (s : List R) (hs : ∀ a ∈ s, a ∈ IsLocalRing.maximalIdeal R)
    [IsArtinianRing (R ⧸ (Ideal.ofList s ⊔ Module.annihilator R M))] :
    chainEuler (coefficientComplex M s) (finiteHomology_of_artinian_support_quotient M s) = 0 := by
  apply koszulDimension_chainEuler_zero M s hs
  rw [Module.supportDim_eq_bot_of_subsingleton]
  exact WithBot.bot_lt_coe _

/-- A repeated equation has zero genuine all-degree Euler characteristic even
for positive-dimensional coefficients. Finiteness concerns only the quotient
by that one equation, and is transported to the actual dependent pair. -/
theorem dependentTwoEquations (M : ModuleCat R) [Module.Finite R M]
    (a : R) (ha : a ∈ IsLocalRing.maximalIdeal R)
    [IsArtinianRing (R ⧸ (Ideal.ofList [a] ⊔ Module.annihilator R M))] :
    ∃ h : FiniteHomology (coefficientComplex M [a, a]),
      chainEuler (coefficientComplex M [a, a]) h = 0 := by
  have hs : ∀ b ∈ [a], b ∈ IsLocalRing.maximalIdeal R := by simpa using ha
  have hd := Motivic.LocalLength.koszulDimension_le_length_of_artinian_support_quotient M [a] hs
  have : IsArtinianRing (R ⧸ (Ideal.ofList [a, a] ⊔ Module.annihilator R M)) := by
    have he : Ideal.ofList [a, a] = Ideal.ofList [a] := by simp
    rw [he]
    infer_instance
  refine ⟨finiteHomology_of_artinian_support_quotient M [a, a], ?_⟩
  apply koszulDimension_chainEuler_zero M [a, a] (by simpa using ha)
  exact hd.trans_lt (by norm_num)

end MotivicTest.KoszulDimensionVanishing
