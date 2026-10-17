/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.RightTripleDiagonalAmbient
public import Motivic.AlgebraicGeometry.Cycles.WholeFiberTorFinite
public import Motivic.AlgebraicGeometry.SmoothSiteNoetherian

/-!
# Right-first whole inverse-image Tor coefficient

The finite map is the unchanged first support times the actual last-pair
scheme-image factor. The coefficient is constructed on its whole target-affine inverse
image, retaining every source branch and the original six-factor Tor charts.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Motivic Motivic.Intersection

universe u

namespace Motivic.MotivicTest.RightWholeFiberTorCoefficient

variable {S X Y Z W : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
  {h : Z ⟶ S} {i : W ⟶ S} [S.IsSeparated]
  [IsSeparated f] [IsSeparated g] [IsSeparated h] [IsSeparated i]
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)

local instance : (correspondenceSixfoldAmbient f g h i).IsSeparated :=
  correspondenceSixfoldAmbient_isSeparated f g h i

/-- The actual coefficient on the entire finite preimage of the original image-product affine. -/
def actualWholeCoefficient (U : (F.rightIntermediateImageProduct G H).affineOpens) (n : ℕ) :
    ((F.rightIntermediateImageMap G H) ⁻¹ᵁ U).toScheme.Modules :=
  wholeFiberTorCoefficient (F.tripleSupportProductInclusion G H)
    (correspondenceSecondAmbientInclusion f g h i) (F.rightIntermediateSupportInclusion G H)
    (F.rightIntermediateToTripleSupport G H) (F.rightIntermediate_ambient_isPullback G H)
    (F.rightIntermediateImageMap G H) U n

/-- Quasi-coherence of the whole original finite-preimage coefficient is derived. -/
instance actualWholeCoefficient_quasicoherent
    (U : (F.rightIntermediateImageProduct G H).affineOpens) (n : ℕ) :
    (actualWholeCoefficient F G H U n).IsQuasicoherent :=
  wholeFiberTorCoefficient_quasicoherent _ _ _ _ _ _ _ _

omit [S.IsSeparated] [IsSeparated f] [IsSeparated g] in
/-- Every original source point over the chosen affine is retained in an actual Tor chart. -/
theorem actualWholeCoefficient_all_branches
    (U : (F.rightIntermediateImageProduct G H).affineOpens)
    {x : F.rightIntermediateSupportProduct G H}
    (hx : x ∈ (F.rightIntermediateImageMap G H) ⁻¹ᵁ U) :
    ∃ r : wholeFiberTorAmbientCover (F.tripleSupportProductInclusion G H)
        (correspondenceSecondAmbientInclusion f g h i) (F.rightIntermediateSupportInclusion G H)
        (F.rightIntermediateToTripleSupport G H) (F.rightIntermediate_ambient_isPullback G H)
        (F.rightIntermediateImageMap G H) U,
      x ∈ (F.rightIntermediateAmbientInclusion G H) ⁻¹ᵁ r.val :=
  wholeFiberTorCoefficient_chart_at _ _ _ _ _ _ _ hx

/-- The whole coefficient has a genuine module over the original inverse-image coordinate ring. -/
def actualWholeSectionModule
    (U : (F.rightIntermediateImageProduct G H).affineOpens) (n : ℕ) :
    ModuleCat.{u} Γ(F.rightIntermediateSupportProduct G H,
      (F.rightIntermediateImageMap G H) ⁻¹ᵁ U) :=
  wholeFiberTorSectionModule (F.tripleSupportProductInclusion G H)
    (correspondenceSecondAmbientInclusion f g h i) (F.rightIntermediateSupportInclusion G H)
    (F.rightIntermediateToTripleSupport G H) (F.rightIntermediate_ambient_isPullback G H)
    (F.rightIntermediateImageMap G H) U n

/-- The actual affine tilde equivalence reconstructs the original whole-preimage sheaf. -/
def actualWholeTildeIso (U : (F.rightIntermediateImageProduct G H).affineOpens) (n : ℕ) :
    (AffineOpenTilde.chartTilde (wholeFiberTorAffineOpen (F.rightIntermediateImageMap G H) U)).obj
      (actualWholeSectionModule F G H U n) ≅ actualWholeCoefficient F G H U n :=
  wholeFiberTorTildeIso _ _ _ _ _ _ _ _

/-- The same original coefficient stalk is attached directly over the original
first-stage support stalk, through its literal open inclusion. -/
def actualWholeOriginalStalkIso
    (U : (F.rightIntermediateImageProduct G H).affineOpens)
    (x : ((F.rightIntermediateImageMap G H) ⁻¹ᵁ U).toScheme) (n : ℕ) :=
  wholeFiberTorCoefficientOriginalStalkIso (F.tripleSupportProductInclusion G H)
    (correspondenceSecondAmbientInclusion f g h i) (F.rightIntermediateSupportInclusion G H)
    (F.rightIntermediateToTripleSupport G H) (F.rightIntermediate_ambient_isPullback G H)
    (F.rightIntermediateImageMap G H) U x n

/-- Original locally finite-type geometry supplies finite whole-coefficient
stalks at every original source point, without genericity or dimension premises. -/
theorem actualWholeStalk_finite [IsLocallyNoetherian S]
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] [LocallyOfFiniteType h]
    [LocallyOfFiniteType i]
    (U : (F.rightIntermediateImageProduct G H).affineOpens)
    (x : ((F.rightIntermediateImageMap G H) ⁻¹ᵁ U).toScheme) (n : ℕ) :
    Module.Finite (((F.rightIntermediateImageMap G H) ⁻¹ᵁ U).toScheme.presheaf.stalk x)
      ((ModuleStalk.functor x).obj
        (wholeFiberTorCoefficient (F.tripleSupportProductInclusion G H)
          (correspondenceSecondAmbientInclusion f g h i) (F.rightIntermediateSupportInclusion G H)
          (F.rightIntermediateToTripleSupport G H) (F.rightIntermediate_ambient_isPullback G H)
          (F.rightIntermediateImageMap G H) U n)) := by
  have := isLocallyNoetherian_correspondenceSixfoldAmbient f g h i
  exact wholeFiberTorCoefficientStalk_finite _ _ _ _ _ _ _ _ _

/-- The actual localized section coefficient uses the full original finite
algebra, not a product of individual source local rings. -/
def actualWholeLocalizedSections
    (U : (F.rightIntermediateImageProduct G H).affineOpens)
    (p : Spec Γ(F.rightIntermediateImageProduct G H, U)) (n : ℕ) :=
  wholeFiberTorLocalizedSections (F.tripleSupportProductInclusion G H)
    (correspondenceSecondAmbientInclusion f g h i) (F.rightIntermediateSupportInclusion G H)
    (F.rightIntermediateToTripleSupport G H) (F.rightIntermediate_ambient_isPullback G H)
    (F.rightIntermediateImageMap G H) U p n

/-- Every actual localized right-first section coefficient is finite, from the
original locally Noetherian geometry and the proved stalk comparison. -/
theorem actualWholeLocalizedSections_finite [IsLocallyNoetherian S]
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] [LocallyOfFiniteType h]
    [LocallyOfFiniteType i]
    (U : (F.rightIntermediateImageProduct G H).affineOpens)
    (p : Spec Γ(F.rightIntermediateImageProduct G H, U)) (n : ℕ) :
    letI : Algebra Γ(F.rightIntermediateImageProduct G H, U)
      Γ(F.rightIntermediateSupportProduct G H, (F.rightIntermediateImageMap G H) ⁻¹ᵁ U) :=
        ((F.rightIntermediateImageMap G H).app U).hom.toAlgebra
    Module.Finite (FiniteFiber.localAlgebra Γ(F.rightIntermediateImageProduct G H, U)
      Γ(F.rightIntermediateSupportProduct G H, (F.rightIntermediateImageMap G H) ⁻¹ᵁ U) p)
      (actualWholeLocalizedSections F G H U p n) := by
  have := isLocallyNoetherian_correspondenceSixfoldAmbient f g h i
  exact wholeFiberTorLocalizedSections_finite _ _ _ _ _ _ _ _ _

section Smooth

variable (K : Type u) [Field K] (X Y Z W : SmoothSite (Spec (.of K)))
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)
  (U : (F.rightIntermediateImageProduct G H).affineOpens)

/-- Every field admits the genuine right-first whole-preimage Tor coefficient,
with quasi-coherence established by its original finite-cover descent. -/
instance actualSmoothWholeCoefficient_quasicoherent (n : ℕ) :
    (actualWholeCoefficient (S := Spec (.of K)) F G H U n).IsQuasicoherent :=
  actualWholeCoefficient_quasicoherent (S := Spec (.of K)) F G H U n

/-- Arbitrary-field smooth-site objects give finite actual whole-preimage
stalks without algebraic closure, nonemptiness or a fixed common dimension. -/
theorem actualSmoothWholeStalk_finite
    (x : ((F.rightIntermediateImageMap G H) ⁻¹ᵁ U).toScheme) (n : ℕ) :
    Module.Finite (((F.rightIntermediateImageMap G H) ⁻¹ᵁ U).toScheme.presheaf.stalk x)
      ((ModuleStalk.functor x).obj
        (actualWholeCoefficient (S := Spec (.of K)) F G H U n)) :=
  actualWholeStalk_finite (S := Spec (.of K)) F G H U x n

/-- The whole semilocal coefficient is finite in each degree over every field;
the actual map remains the first-support identity times the last-pair image factor. -/
theorem actualSmoothWholeLocalizedSections_finite
    (p : Spec Γ(F.rightIntermediateImageProduct G H, U)) (n : ℕ) :
    letI : Algebra Γ(F.rightIntermediateImageProduct G H, U)
      Γ(F.rightIntermediateSupportProduct G H, (F.rightIntermediateImageMap G H) ⁻¹ᵁ U) :=
        ((F.rightIntermediateImageMap G H).app U).hom.toAlgebra
    Module.Finite (FiniteFiber.localAlgebra Γ(F.rightIntermediateImageProduct G H, U)
      Γ(F.rightIntermediateSupportProduct G H, (F.rightIntermediateImageMap G H) ⁻¹ᵁ U) p)
      (actualWholeLocalizedSections (S := Spec (.of K)) F G H U p n) :=
  actualWholeLocalizedSections_finite (S := Spec (.of K)) F G H U p n

end Smooth

end Motivic.MotivicTest.RightWholeFiberTorCoefficient
