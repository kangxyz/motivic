/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulPairSupportEuler

/-!
# Support-sensitive Euler consumers for actual submodule quotient sequences

The maps here are the actual inclusion of a submodule and its quotient map.
The finite-homology witnesses and the Euler equality are all derived from the
support of the middle module, with no assumed finite homology or regular pair.
-/

@[expose] public section

universe u v

open Motivic.LocalLength.KoszulPair

namespace MotivicTest.KoszulPairSupportEuler

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
variable (P : Submodule R M) (a b : R)

/-- A genuine submodule quotient sequence has finite homology and additive Euler
multiplicity when its middle support intersection is Artinian. -/
theorem submodule_euler_add_of_artinian_support
    [IsArtinianRing (R ⧸ (Ideal.span ({a, b} : Set R) ⊔ Module.annihilator R M))] :
    ∃ (hP : HasFiniteHomology P a b) (hM : HasFiniteHomology M a b)
      (hQ : HasFiniteHomology (M ⧸ P) a b),
      eulerMultiplicity M a b hM =
        eulerMultiplicity P a b hP + eulerMultiplicity (M ⧸ P) a b hQ :=
  ⟨_, _, _, eulerMultiplicity_add_of_artinian_middle_support_quotient a b P.subtype P.mkQ
    P.subtype_injective P.mkQ_surjective (LinearMap.exact_subtype_mkQ P)⟩

/-- The local minimal-prime criterion supplies both finite homology and Euler
additivity for the actual submodule quotient sequence. -/
theorem submodule_euler_add_of_mem_minimalPrimes_support [IsLocalRing R]
    (hm : IsLocalRing.maximalIdeal R ∈
      (Ideal.span ({a, b} : Set R) ⊔ Module.annihilator R M).minimalPrimes) :
    ∃ (hP : HasFiniteHomology P a b) (hM : HasFiniteHomology M a b)
      (hQ : HasFiniteHomology (M ⧸ P) a b),
      eulerMultiplicity M a b hM =
        eulerMultiplicity P a b hP + eulerMultiplicity (M ⧸ P) a b hQ :=
  ⟨_, _, _, eulerMultiplicity_add_of_mem_minimalPrimes_middle_support a b P.subtype P.mkQ
    P.subtype_injective P.mkQ_surjective (LinearMap.exact_subtype_mkQ P) hm⟩

end MotivicTest.KoszulPairSupportEuler
