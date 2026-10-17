/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.IntermediateDiagonalLists
public import Motivic.Algebra.Homology.KoszulCoefficientComplex
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Actual remaining-list scalar and localization consumers

The same original middle list is tracked at actual triple points, in every
actual first-stage stalk module, after prime localization, and in its literal
coefficient Koszul complex. The image-product map has the correct finite
fiber under separatedness; no individual source stalk is asserted finite.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic.MotivicTest.IntermediateDiagonalLists

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)

/-- An original common-middle list at an actual triple point feeds both
literal remaining-list routes through the actual first-stage support. -/
theorem actualTripleOriginalList (w : F.tripleIncidence G H)
    (s : List ((CategoryTheory.Limits.pullback h h).presheaf.stalk
      (correspondenceSixfoldSecondMiddlePair f g h i (F.tripleIncidenceSixfoldInclusion G H w)))) :
    let u := F.tripleIncidenceToLeftSupportProduct G H w
    let s' := s.map (F.tripleRemainingMiddleStalkIso G H w).hom.hom
    (s'.map (F.leftImageMiddleStalkMap G H u).hom).map
        ((F.leftIntermediateImageMap G H).stalkMap u).hom =
      (s'.map (F.leftAmbientMiddleStalkMap G H u).hom).map
        ((F.leftIntermediateAmbientInclusion G H).stalkMap u).hom :=
  F.leftRemainingList_square G H _ _

/-- The two literal scalar routes act identically on every actual first-stage
stalk module, with no transported replacement action. -/
theorem actualRemainingScalar (w : F.leftIntermediateSupportProduct G H)
    (M : ModuleCat ((F.leftIntermediateSupportProduct G H).presheaf.stalk w))
    (a : (CategoryTheory.Limits.pullback h h).presheaf.stalk (F.leftSupportMiddlePair G H w))
    (m : M) :
    (F.leftIntermediateImageMap G H).stalkMap w (F.leftImageMiddleStalkMap G H w a) • m =
      (F.leftIntermediateAmbientInclusion G H).stalkMap w
        (F.leftAmbientMiddleStalkMap G H w a) • m := by
  have he := (F.leftImageMiddleStalkMap_comp G H w).trans
    (F.leftAmbientMiddleStalkMap_comp G H w).symm
  exact congrArg (fun r => r • m) (ConcreteCategory.congr_hom he a)

/-- The same actual lists remain identical after literal prime localization
of the source stalk, with no finite-local-ring assertion. -/
theorem actualLocalizedRemainingList (w : F.leftIntermediateSupportProduct G H)
    (q : PrimeSpectrum ((F.leftIntermediateSupportProduct G H).presheaf.stalk w))
    (s : List ((CategoryTheory.Limits.pullback h h).presheaf.stalk
      (F.leftSupportMiddlePair G H w))) :
    ((s.map (F.leftImageMiddleStalkMap G H w).hom).map
        ((F.leftIntermediateImageMap G H).stalkMap w).hom).map
          (algebraMap ((F.leftIntermediateSupportProduct G H).presheaf.stalk w)
            (Localization.AtPrime q.asIdeal)) =
      ((s.map (F.leftAmbientMiddleStalkMap G H w).hom).map
        ((F.leftIntermediateAmbientInclusion G H).stalkMap w).hom).map
          (algebraMap ((F.leftIntermediateSupportProduct G H).presheaf.stalk w)
            (Localization.AtPrime q.asIdeal)) :=
  congrArg (List.map (algebraMap ((F.leftIntermediateSupportProduct G H).presheaf.stalk w)
    (Localization.AtPrime q.asIdeal))) (F.leftRemainingList_square G H w s)

/-- The actual second-stage coefficient complexes use identical equations
after the proved geometric scalar squares, rather than an assumed list equality. -/
def actualRemainingCoefficientIso (w : F.leftIntermediateSupportProduct G H)
    (M : ModuleCat ((F.leftIntermediateSupportProduct G H).presheaf.stalk w))
    (s : List ((CategoryTheory.Limits.pullback h h).presheaf.stalk
      (F.leftSupportMiddlePair G H w))) :
    Koszul.coefficientComplex M
        ((s.map (F.leftImageMiddleStalkMap G H w).hom).map
          ((F.leftIntermediateImageMap G H).stalkMap w).hom) ≅
      Koszul.coefficientComplex M
        ((s.map (F.leftAmbientMiddleStalkMap G H w).hom).map
          ((F.leftIntermediateAmbientInclusion G H).stalkMap w).hom) :=
  eqToIso (congrArg (Koszul.coefficientComplex M) (F.leftRemainingList_square G H w s))

/-- The relevant finite fiber is that of the true intermediate-image product
map, without using the generally nonfinite right-pair projection. -/
theorem actualIntermediateImageFiber [IsSeparated h] (y : F.leftIntermediateImageProduct G H) :
    Set.Finite (F.leftIntermediateImageMap G H ⁻¹' {y}) :=
  (F.leftIntermediateImageMap G H).finite_preimage_singleton y

end Motivic.MotivicTest.IntermediateDiagonalLists
