/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.Koszul.Pair.EulerAdditivity
public import Motivic.Aglib.RingTheory.LocalLength.KoszulPairLocalSupport

/-!
# Euler additivity from the middle coefficient support

For a short exact coefficient sequence, the annihilator of the middle module
annihilates both end modules. Artinianness of the equation intersection with
that single support therefore supplies the finite homology needed for the
actual Koszul long-exact-sequence Euler theorem. A local minimal-prime version
discharges the Artinian hypothesis as well. No regularity is assumed.
-/

@[expose] public section

universe u v

namespace Module.KoszulPair

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {U V W : Type v}
variable [AddCommGroup U] [Module R U] [Module.Finite R U]
variable [AddCommGroup V] [Module R V] [Module.Finite R V]
variable [AddCommGroup W] [Module R W] [Module.Finite R W]
variable (a b : R)

/-- The support of the middle coefficient module alone controls finite length
and Euler additivity throughout a short exact sequence. -/
theorem eulerMultiplicity_add_of_artinian_middle_support_quotient
    [IsArtinianRing (R ⧸ (Ideal.span ({a, b} : Set R) ⊔ Module.annihilator R V))]
    (f : U →ₗ[R] V) (g : V →ₗ[R] W)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hex : Function.Exact f g) :
    eulerMultiplicity V a b (hasFiniteHomology_of_artinian_support_quotient V a b) =
      eulerMultiplicity U a b
        (hasFiniteHomology_of_artinian_quotient_of_le_annihilator U a b
          (Module.annihilator R V) (f.annihilator_le_of_injective hf)) +
      eulerMultiplicity W a b
        (hasFiniteHomology_of_artinian_quotient_of_le_annihilator W a b
          (Module.annihilator R V) (g.annihilator_le_of_surjective hg)) :=
  eulerMultiplicity_add_of_exact a b f g hf hg hex _ _ _

/-- Minimality of the local maximal ideal over the middle coefficient support
intersection supplies every finite-length hypothesis in the Euler additive law. -/
theorem eulerMultiplicity_add_of_mem_minimalPrimes_middle_support
    [IsLocalRing R]
    (f : U →ₗ[R] V) (g : V →ₗ[R] W)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hex : Function.Exact f g)
    (hm : IsLocalRing.maximalIdeal R ∈
      (Ideal.span ({a, b} : Set R) ⊔ Module.annihilator R V).minimalPrimes) :
    eulerMultiplicity V a b (hasFiniteHomology_of_mem_minimalPrimes_support V a b hm) =
      eulerMultiplicity U a b
        (hasFiniteHomology_of_mem_minimalPrimes_of_le_annihilator U a b
          (Module.annihilator R V) (f.annihilator_le_of_injective hf) hm) +
      eulerMultiplicity W a b
        (hasFiniteHomology_of_mem_minimalPrimes_of_le_annihilator W a b
          (Module.annihilator R V) (g.annihilator_le_of_surjective hg) hm) :=
  eulerMultiplicity_add_of_exact a b f g hf hg hex _ _ _

end Module.KoszulPair
