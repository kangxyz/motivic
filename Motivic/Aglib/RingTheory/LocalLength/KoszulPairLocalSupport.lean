/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.LocalLength.KoszulPairSupport
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Finite Koszul homology at a minimal local support prime

In a Noetherian local ring, minimality of the maximal ideal over the equations
and a coefficient-annihilating ideal makes the corresponding quotient Artinian.
The support-sensitive Koszul annihilation theorem then proves finite length of
all three actual homology modules. This is a local algebra criterion, not a
construction of equations or support primes from a geometric intersection.
-/

@[expose] public section

universe u v

namespace Module.KoszulPair

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] (a b : R)

/-- Minimality of the local maximal ideal over the equations and an annihilating
ideal supplies finite length of each actual Koszul homology module. -/
theorem hasFiniteHomology_of_mem_minimalPrimes_of_le_annihilator
    (I : Ideal R) (hI : I ≤ Module.annihilator R M)
    (hm : IsLocalRing.maximalIdeal R ∈ (Ideal.span ({a, b} : Set R) ⊔ I).minimalPrimes) :
    HasFiniteHomology M a b := by
  have : IsArtinianRing (R ⧸ (Ideal.span ({a, b} : Set R) ⊔ I)) :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _ hm
  exact hasFiniteHomology_of_artinian_quotient_of_le_annihilator M a b I hI

/-- At a minimal prime of the equation intersection with the coefficient support,
the actual two-element Koszul homology has finite length, without regularity. -/
theorem hasFiniteHomology_of_mem_minimalPrimes_support
    (hm : IsLocalRing.maximalIdeal R ∈
      (Ideal.span ({a, b} : Set R) ⊔ Module.annihilator R M).minimalPrimes) :
    HasFiniteHomology M a b :=
  hasFiniteHomology_of_mem_minimalPrimes_of_le_annihilator M a b
    (Module.annihilator R M) le_rfl hm

end Module.KoszulPair
