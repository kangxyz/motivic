/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulFiniteSupport
public import Motivic.RingTheory.LocalLength.ArtinianQuotient
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Finite length of arbitrary finite Koszul homology on coefficient support

Actual coefficient Koszul homology has finite length whenever the base is
Noetherian, the coefficient module is finite, and the quotient by the equations
plus the coefficient annihilator is Artinian. A local minimal-prime criterion
supplies that Artinian hypothesis. All list lengths and all homological degrees
are covered, with no regularity assumption on either the ring or the module.
-/

@[expose] public section

universe u

namespace Module.KoszulFinite

open Motivic.Koszul

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (M : ModuleCat R) [Module.Finite R M] (s : List R)

/-- An Artinian quotient by the equations and a coefficient-annihilating ideal
makes every actual finite Koszul homology module finite-length. -/
theorem length_homology_ne_top_of_artinian_quotient_of_le_annihilator
    (I : Ideal R) [IsArtinianRing (R ⧸ (Ideal.ofList s ⊔ I))]
    (hI : I ≤ Module.annihilator R M) (n : ℕ) :
    Module.length R ((coefficientComplex M s).homology n) ≠ ⊤ :=
  length_ne_top_of_artinian_quotient ((coefficientComplex M s).homology n)
    (Ideal.ofList s ⊔ I) (sup_le (ofList_le_annihilator_coefficient_homology M s n)
      (hI.trans (coefficient_annihilator_le_annihilator_homology M s n)))

/-- Artinianness on coefficient support proves finite length in every actual degree. -/
theorem length_homology_ne_top_of_artinian_support_quotient
    [IsArtinianRing (R ⧸ (Ideal.ofList s ⊔ Module.annihilator R M))] (n : ℕ) :
    Module.length R ((coefficientComplex M s).homology n) ≠ ⊤ :=
  length_homology_ne_top_of_artinian_quotient_of_le_annihilator M s
    (Module.annihilator R M) le_rfl n

/-- Minimality of the maximal ideal over equations and a coefficient-annihilating
ideal proves finite length of arbitrary finite-list Koszul homology. -/
theorem length_homology_ne_top_of_mem_minimalPrimes_of_le_annihilator
    [IsLocalRing R] (I : Ideal R) (hI : I ≤ Module.annihilator R M)
    (hm : IsLocalRing.maximalIdeal R ∈ (Ideal.ofList s ⊔ I).minimalPrimes) (n : ℕ) :
    Module.length R ((coefficientComplex M s).homology n) ≠ ⊤ := by
  have : IsArtinianRing (R ⧸ (Ideal.ofList s ⊔ I)) :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _ hm
  exact length_homology_ne_top_of_artinian_quotient_of_le_annihilator M s I hI n

/-- At a minimal local support prime, every actual finite Koszul homology module
has finite length, without any regularity hypothesis. -/
theorem length_homology_ne_top_of_mem_minimalPrimes_support [IsLocalRing R]
    (hm : IsLocalRing.maximalIdeal R ∈
      (Ideal.ofList s ⊔ Module.annihilator R M).minimalPrimes) (n : ℕ) :
    Module.length R ((coefficientComplex M s).homology n) ≠ ⊤ :=
  length_homology_ne_top_of_mem_minimalPrimes_of_le_annihilator M s
    (Module.annihilator R M) le_rfl hm n

end Module.KoszulFinite
