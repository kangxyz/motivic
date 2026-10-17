/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Intersection.ClosedAffineOverlap
public import Motivic.AlgebraicGeometry.Intersection.ClosedIntersectionTorSheafRestriction
public import Motivic.AlgebraicGeometry.SmoothSite

/-!
# Genuine smooth-site ambient overlaps and original Tor refinements

Separatedness comes from the original structure maps. The overlap refinement
acts on the actual first-stage exterior Tor sheaves, not abstract replacements.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Motivic Motivic.Intersection

universe u

namespace Motivic.MotivicTest.ClosedAffineOverlap

section General

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  [S.IsSeparated] [IsSeparated f] [IsSeparated g] [IsSeparated h] [IsSeparated i]
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)

local instance : (correspondenceSixfoldAmbient f g h i).IsSeparated :=
  correspondenceSixfoldAmbient_isSeparated f g h i

/-- Original incidence chart intersections are literal preimages of the actual affine overlap. -/
theorem actualClosedChartOverlap
    (U V : (correspondenceSixfoldAmbient f g h i).affineOpens) :
    (F.leftIntermediateAmbientInclusion G H) ⁻¹ᵁ
        (ClosedAffineCover.affineOverlap U V).1 =
      ((F.leftIntermediateAmbientInclusion G H) ⁻¹ᵁ U) ⊓
        ((F.leftIntermediateAmbientInclusion G H) ⁻¹ᵁ V) :=
  ClosedAffineCover.preimage_affineOverlap _ U V

/-- The actual left Tor sheaf has a genuine restriction to the shared overlap chart. -/
def actualLeftTorOverlap
    (U V : (correspondenceSixfoldAmbient f g h i).affineOpens) (n : ℕ) :=
  closedIntersectionTorSheafRestrictionIso (F.tripleSupportProductInclusion G H)
    (correspondenceFirstDiagonalInclusion f g h i)
    (F.leftIntermediateSupportInclusion G H) (F.leftIntermediateToTripleSupport G H)
    (F.leftIntermediate_ambient_isPullback G H)
    (ClosedAffineCover.affineOverlap_le_left U V) n

/-- The actual right Tor sheaf restricts to exactly the same ambient overlap chart. -/
def actualRightTorOverlap
    (U V : (correspondenceSixfoldAmbient f g h i).affineOpens) (n : ℕ) :=
  closedIntersectionTorSheafRestrictionIso (F.tripleSupportProductInclusion G H)
    (correspondenceFirstDiagonalInclusion f g h i)
    (F.leftIntermediateSupportInclusion G H) (F.leftIntermediateToTripleSupport G H)
    (F.leftIntermediate_ambient_isPullback G H)
    (ClosedAffineCover.affineOverlap_le_right U V) n

end General

/-- Every actual smooth separated finite-type four-tuple over a field has a separated ambient. -/
theorem actualSmoothSiteAmbientSeparated (K : Type u) [Field K]
    (X Y Z W : SmoothSite (Spec (CommRingCat.of K))) :
    (correspondenceSixfoldAmbient X.hom Y.hom Z.hom W.hom).IsSeparated :=
  correspondenceSixfoldAmbient_isSeparated (S := Spec (CommRingCat.of K))
    X.hom Y.hom Z.hom W.hom

/-- Affineness of actual smooth-site overlaps is derived, with no integral-component assumption. -/
theorem actualSmoothSiteOverlapAffine (K : Type u) [Field K]
    (X Y Z W : SmoothSite (Spec (CommRingCat.of K)))
    (U V : (correspondenceSixfoldAmbient X.hom Y.hom Z.hom W.hom).affineOpens) :
    IsAffineOpen (U.1 ⊓ V.1) :=
  correspondenceSixfoldAffineOverlap (S := Spec (CommRingCat.of K))
    X.hom Y.hom Z.hom W.hom U V

end Motivic.MotivicTest.ClosedAffineOverlap
