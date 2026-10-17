/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulFiniteIdeal

/-!
# Consumers of genuine arbitrary-finite Koszul complexes

The examples use actual chain complexes, their differentials and homology,
and their projective terms. The regularity hypothesis is used only for the
proved one-element resolution; no arbitrary-list resolution is assumed.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Motivic.Koszul

variable {R : Type u} [CommRing R]
variable (a b c : R) (s t : List R)

example (x : R) : (singleComplex R a).d 1 0 x = a * x := rfl

example : chainComplex ([] : List R) =
    HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.down ℕ) := rfl

example : chainComplex [a] ≅ singleComplex R a := singletonIso a

example : chainComplex (s ++ t) ≅
    HomologicalComplex.tensorObj (chainComplex s) (chainComplex t) := appendIso s t

example : Projective ((chainComplex [a, b, c]).X 2) := chainComplex_projective _ _

example : IsZero ((chainComplex [a, b, c]).X 4) := isZero_X _ _ (by simp)

example : (chainComplex [a, b, c]).ExactAt 4 := exactAt_above_length _ _ (by simp)

example : (chainComplex s).X 0 ≅ ModuleCat.of R R := zeroComponentIso s

example : (chainComplex s).homology 0 ≅ ModuleCat.of R (HomologyZeroQuotient s) :=
  homologyZeroIso s

example : QuasiIsoAt (augmentation s) 0 := augmentation_quasiIsoAt_zero s

example (ha : IsSMulRegular R a) :
    ProjectiveResolution (ModuleCat.of R (SingleQuotient R a)) :=
  singleProjectiveResolution R a ha

example (ha : IsSMulRegular R a) : (chainComplex [a]).ExactAt 1 :=
  (singleExactAt_one_of_regular R a ha).of_iso (singletonIso a).symm

example (n : ℕ) :
    ιCons a s 1 (n + 1) (n + 2) (by omega) ≫
        (chainComplex (a :: s)).d (n + 2) (n + 1) =
      (ModuleCat.ofHom (LinearMap.lsmul R R a) ▷ (chainComplex s).X (n + 1)) ≫
          ιCons a s 0 (n + 1) (n + 1) (by omega) -
        ((ModuleCat.of R R) ◁ (chainComplex s).d (n + 1) n) ≫
          ιCons a s 1 n (n + 1) (by omega) :=
  ιCons_one_d a s n

example : boundaryIdeal s = Ideal.ofList s := boundaryIdeal_eq_ofList s

example : (chainComplex s).homology 0 ≅ ModuleCat.of R (R ⧸ Ideal.ofList s) :=
  homologyZeroIdealIso s

example : QuasiIsoAt (idealAugmentation s) 0 := idealAugmentation_quasiIsoAt_zero s
