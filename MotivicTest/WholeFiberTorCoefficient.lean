/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Intersection.WholeFiberTorCoefficient

/-!
# Whole original image-product inverse-image coefficient

The finite map is the actual pair-to-image morphism times the unchanged third
support. The coefficient is constructed on its whole target-affine inverse
image, retaining every source branch and the original six-factor Tor charts.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Motivic Motivic.Intersection

universe u

namespace Motivic.MotivicTest.WholeFiberTorCoefficient

variable {S X Y Z W : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
  {h : Z ⟶ S} {i : W ⟶ S} [S.IsSeparated]
  [IsSeparated f] [IsSeparated g] [IsSeparated h] [IsSeparated i]
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)

local instance : (correspondenceSixfoldAmbient f g h i).IsSeparated :=
  correspondenceSixfoldAmbient_isSeparated f g h i

/-- The actual coefficient on the entire finite preimage of the original image-product affine. -/
def actualWholeCoefficient (U : (F.leftIntermediateImageProduct G H).affineOpens) (n : ℕ) :
    ((F.leftIntermediateImageMap G H) ⁻¹ᵁ U).toScheme.Modules :=
  wholeFiberTorCoefficient (F.tripleSupportProductInclusion G H)
    (correspondenceFirstDiagonalInclusion f g h i) (F.leftIntermediateSupportInclusion G H)
    (F.leftIntermediateToTripleSupport G H) (F.leftIntermediate_ambient_isPullback G H)
    (F.leftIntermediateImageMap G H) U n

/-- Quasi-coherence of the whole original finite-preimage coefficient is derived. -/
instance actualWholeCoefficient_quasicoherent
    (U : (F.leftIntermediateImageProduct G H).affineOpens) (n : ℕ) :
    (actualWholeCoefficient F G H U n).IsQuasicoherent :=
  wholeFiberTorCoefficient_quasicoherent _ _ _ _ _ _ _ _

omit [S.IsSeparated] [IsSeparated f] [IsSeparated i] in
/-- Every original source point over the chosen affine is retained in an actual Tor chart. -/
theorem actualWholeCoefficient_all_branches
    (U : (F.leftIntermediateImageProduct G H).affineOpens)
    {x : F.leftIntermediateSupportProduct G H}
    (hx : x ∈ (F.leftIntermediateImageMap G H) ⁻¹ᵁ U) :
    ∃ r : wholeFiberTorAmbientCover (F.tripleSupportProductInclusion G H)
        (correspondenceFirstDiagonalInclusion f g h i) (F.leftIntermediateSupportInclusion G H)
        (F.leftIntermediateToTripleSupport G H) (F.leftIntermediate_ambient_isPullback G H)
        (F.leftIntermediateImageMap G H) U,
      x ∈ (F.leftIntermediateAmbientInclusion G H) ⁻¹ᵁ r.val :=
  wholeFiberTorCoefficient_chart_at _ _ _ _ _ _ _ hx

/-- The whole coefficient has a genuine module over the original inverse-image coordinate ring. -/
def actualWholeSectionModule
    (U : (F.leftIntermediateImageProduct G H).affineOpens) (n : ℕ) :
    ModuleCat.{u} Γ(F.leftIntermediateSupportProduct G H,
      (F.leftIntermediateImageMap G H) ⁻¹ᵁ U) :=
  wholeFiberTorSectionModule (F.tripleSupportProductInclusion G H)
    (correspondenceFirstDiagonalInclusion f g h i) (F.leftIntermediateSupportInclusion G H)
    (F.leftIntermediateToTripleSupport G H) (F.leftIntermediate_ambient_isPullback G H)
    (F.leftIntermediateImageMap G H) U n

/-- The actual affine tilde equivalence reconstructs the original whole-preimage sheaf. -/
def actualWholeTildeIso (U : (F.leftIntermediateImageProduct G H).affineOpens) (n : ℕ) :
    (AffineOpenTilde.chartTilde (wholeFiberTorAffineOpen (F.leftIntermediateImageMap G H) U)).obj
      (actualWholeSectionModule F G H U n) ≅ actualWholeCoefficient F G H U n :=
  wholeFiberTorTildeIso _ _ _ _ _ _ _ _

end Motivic.MotivicTest.WholeFiberTorCoefficient
