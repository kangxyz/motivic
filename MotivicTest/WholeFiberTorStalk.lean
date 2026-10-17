/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Intersection.WholeFiberTorStalk
public import Motivic.AlgebraicGeometry.SmoothSiteNoetherian

/-!
# Original whole-fiber first-stage Tor stalk consumers

The finite map is the actual pair-to-image morphism times the unchanged third
support. Every stalk of the constructed whole inverse-image coefficient is
attached to original supported Tor, with genuine original structure-ring maps.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Motivic Motivic.Intersection

universe u

namespace MotivicTest.WholeFiberTorStalk

variable {S X Y Z W : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
  {h : Z ⟶ S} {i : W ⟶ S} [S.IsSeparated]
  [IsSeparated f] [IsSeparated g] [IsSeparated h] [IsSeparated i]
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)

local instance : (correspondenceSixfoldAmbient f g h i).IsSeparated :=
  correspondenceSixfoldAmbient_isSeparated f g h i

/-- The original first-stage equalizer stalk, at any actual whole-preimage point,
is the existing supported Tor with its original intersection structure ring. -/
def actualWholeGluedStalkIso
    (U : (F.leftIntermediateImageProduct G H).affineOpens)
    (w : F.leftIntermediateSupportProduct G H)
    (hw : w ∈ (F.leftIntermediateImageMap G H) ⁻¹ᵁ U) (n : ℕ) :=
  wholeFiberTorGluedStalkIso (F.tripleSupportProductInclusion G H)
    (correspondenceFirstDiagonalInclusion f g h i) (F.leftIntermediateSupportInclusion G H)
    (F.leftIntermediateToTripleSupport G H) (F.leftIntermediate_ambient_isPullback G H)
    (F.leftIntermediateImageMap G H) U w hw n

/-- The actual whole first-stage coefficient stalk is compared over its genuine
open-subscheme local ring using the inverse original inclusion stalk map. -/
def actualWholeStalkIso
    (U : (F.leftIntermediateImageProduct G H).affineOpens)
    (x : ((F.leftIntermediateImageMap G H) ⁻¹ᵁ U).toScheme) (n : ℕ) :=
  wholeFiberTorCoefficientStalkIso (F.tripleSupportProductInclusion G H)
    (correspondenceFirstDiagonalInclusion f g h i) (F.leftIntermediateSupportInclusion G H)
    (F.leftIntermediateToTripleSupport G H) (F.leftIntermediate_ambient_isPullback G H)
    (F.leftIntermediateImageMap G H) U x n

/-- The same original coefficient stalk is attached directly over the original
first-stage support stalk, through its literal open inclusion. -/
def actualWholeOriginalStalkIso
    (U : (F.leftIntermediateImageProduct G H).affineOpens)
    (x : ((F.leftIntermediateImageMap G H) ⁻¹ᵁ U).toScheme) (n : ℕ) :=
  wholeFiberTorCoefficientOriginalStalkIso (F.tripleSupportProductInclusion G H)
    (correspondenceFirstDiagonalInclusion f g h i) (F.leftIntermediateSupportInclusion G H)
    (F.leftIntermediateToTripleSupport G H) (F.leftIntermediate_ambient_isPullback G H)
    (F.leftIntermediateImageMap G H) U x n

/-- Original locally finite-type geometry supplies finite whole-coefficient
stalks at every original source point, without genericity or dimension premises. -/
theorem actualWholeStalk_finite [IsLocallyNoetherian S]
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] [LocallyOfFiniteType h]
    [LocallyOfFiniteType i]
    (U : (F.leftIntermediateImageProduct G H).affineOpens)
    (x : ((F.leftIntermediateImageMap G H) ⁻¹ᵁ U).toScheme) (n : ℕ) :
    Module.Finite (((F.leftIntermediateImageMap G H) ⁻¹ᵁ U).toScheme.presheaf.stalk x)
      ((ModuleStalk.functor x).obj
        (wholeFiberTorCoefficient (F.tripleSupportProductInclusion G H)
          (correspondenceFirstDiagonalInclusion f g h i) (F.leftIntermediateSupportInclusion G H)
          (F.leftIntermediateToTripleSupport G H) (F.leftIntermediate_ambient_isPullback G H)
          (F.leftIntermediateImageMap G H) U n)) := by
  have := isLocallyNoetherian_correspondenceSixfoldAmbient f g h i
  exact wholeFiberTorCoefficientStalk_finite _ _ _ _ _ _ _ _ _

local instance smoothSixfoldSeparated (K : Type u) [Field K]
    (X Y Z W : SmoothSite (Spec (.of K))) :
    (correspondenceSixfoldAmbient X.hom Y.hom Z.hom W.hom).IsSeparated :=
  correspondenceSixfoldAmbient_isSeparated (S := Spec (.of K)) X.hom Y.hom Z.hom W.hom

/-- Smooth-site objects over every field satisfy actual whole-coefficient stalk
finiteness; no auxiliary noetherian-ring or nonempty assumption is imposed. -/
theorem actualSmoothWholeStalk_finite (K : Type u) [Field K]
    (X Y Z W : SmoothSite (Spec (.of K)))
    (F : FiniteCorrespondenceGenerator X.hom Y.hom)
    (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
    (H : FiniteCorrespondenceGenerator Z.hom W.hom)
    (U : (F.leftIntermediateImageProduct G H).affineOpens)
    (x : ((F.leftIntermediateImageMap G H) ⁻¹ᵁ U).toScheme) (n : ℕ) :
    Module.Finite (((F.leftIntermediateImageMap G H) ⁻¹ᵁ U).toScheme.presheaf.stalk x)
      ((ModuleStalk.functor x).obj
        (wholeFiberTorCoefficient (F.tripleSupportProductInclusion G H)
          (correspondenceFirstDiagonalInclusion X.hom Y.hom Z.hom W.hom)
          (F.leftIntermediateSupportInclusion G H) (F.leftIntermediateToTripleSupport G H)
          (F.leftIntermediate_ambient_isPullback G H) (F.leftIntermediateImageMap G H) U n)) :=
  actualWholeStalk_finite (S := Spec (.of K)) F G H U x n

end MotivicTest.WholeFiberTorStalk
