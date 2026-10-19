/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.Koszul.Pair.Tor
public import Motivic.Aglib.Algebra.Homology.Koszul.Pair.Ideal

/-!
# Consumers of the actual Koszul resolution and Tor comparison

These checks use the public chain-complex, projective-resolution and Tor APIs.
They retain the ring-regularity hypotheses in the arbitrary-module Tor theorem.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open Module.KoszulPair

variable {R : Type u} [CommRing R]
variable (M : Type u) [AddCommGroup M] [Module R M] (a b : R)
variable (ha : IsSMulRegular R a) (hb : IsSMulRegular (PrincipalQuotient R a) b)

example (z : M) : (chainComplex M a b).d 2 1 z = (-(b • z), a • z) := rfl

example (z : M × M) : (chainComplex M a b).d 1 0 z = a • z.1 + b • z.2 := rfl

example : ProjectiveResolution (ModuleCat.of R (R ⧸ Ideal.span ({a, b} : Set R))) :=
  idealProjectiveResolution a b ha hb

example : (projectiveResolution R a b ha hb).complex = chainComplex R a b := rfl

example : QuasiIso (projectiveResolution R a b ha hb).π := inferInstance

example :
    ((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj
      (ModuleCat.of R (H₀ R a b)) ≅ ModuleCat.of R (H₁ M a b) :=
  torOneIso M a b ha hb

example :
    ((Tor (ModuleCat R) 2).obj (ModuleCat.of R M)).obj
      (ModuleCat.of R (H₀ R a b)) ≅ ModuleCat.of R (H₂ M a b) :=
  torTwoIso M a b ha hb

example :
    ((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj
      (ModuleCat.of R (R ⧸ Ideal.span ({a, b} : Set R))) ≅ ModuleCat.of R (H₁ M a b) :=
  torIdealIsoHomology M a b ha hb 1 ≪≫ homologyOneIso M a b

include ha hb in
example (n : ℕ) : IsZero (((Tor (ModuleCat R) (n + 3)).obj (ModuleCat.of R M)).obj
    (ModuleCat.of R (H₀ R a b))) :=
  isZero_tor_add_three M a b ha hb n
