/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Motivic.Aglib.Algebra.Homology.Koszul.Pair.EulerAdditivity

/-!
# Consumers of the local Koszul and genuine Tor Euler comparison

These checks retain higher homology and only require regularity on the ring
for the Tor comparison, not regularity on the coefficient module.
-/

open CategoryTheory _root_.HomologicalComplex.ModuleLengthEuler Module.KoszulPair

universe u v

namespace MotivicTest.KoszulPairEuler

variable {R : Type u} [CommRing R]

example (M : Type v) [AddCommGroup M] [Module R M] (a b : R)
    (h : HasFiniteHomology M a b) :
    chainEuler (chainComplex M a b) (finiteHomology_chainComplex M a b h) =
      eulerMultiplicity M a b h :=
  chainEuler_eq_eulerMultiplicity M a b h

example (M : Type u) [AddCommGroup M] [Module R M] (a b : R)
    (ha : IsSMulRegular R a) (hb : IsSMulRegular (PrincipalQuotient R a) b)
    (h : HasFiniteHomology M a b) :
    signedLengthSum (fun n =>
      ((Tor (ModuleCat R) n).obj (ModuleCat.of R M)).obj (ModuleCat.of R (H₀ R a b)))
      (fun n => (-1) ^ n) (finiteLengthSupport_tor a b M ha hb h) =
      eulerMultiplicity M a b h :=
  torEuler_eq_eulerMultiplicity a b M ha hb h

example {U V W : Type v}
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] (a b : R)
    (f : U →ₗ[R] V) (g : V →ₗ[R] W)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hex : Function.Exact f g)
    (hU : HasFiniteHomology U a b) (hV : HasFiniteHomology V a b)
    (hW : HasFiniteHomology W a b) :
    eulerMultiplicity V a b hV = eulerMultiplicity U a b hU + eulerMultiplicity W a b hW :=
  eulerMultiplicity_add_of_exact a b f g hf hg hex hU hV hW

example {U V W : Type v}
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] [IsNoetherianRing R]
    [Module.Finite R U] [Module.Finite R V] [Module.Finite R W] (a b : R)
    [IsArtinianRing (R ⧸ Ideal.span ({a, b} : Set R))]
    (f : U →ₗ[R] V) (g : V →ₗ[R] W)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hex : Function.Exact f g) :
    eulerMultiplicity V a b (hasFiniteHomology_of_artinian_quotient V a b) =
      eulerMultiplicity U a b (hasFiniteHomology_of_artinian_quotient U a b) +
        eulerMultiplicity W a b (hasFiniteHomology_of_artinian_quotient W a b) :=
  eulerMultiplicity_add_of_artinian_quotient a b f g hf hg hex

end MotivicTest.KoszulPairEuler
