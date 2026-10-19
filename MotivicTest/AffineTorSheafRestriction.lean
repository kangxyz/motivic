/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Intersection.ClosedIntersectionTorSheafRestriction
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Associativity.DiagonalAmbient

/-!
# Genuine affine and finite-correspondence Tor sheaf restrictions

The actual pair and six-factor first-stage chart sheaves restrict through the
constructed geometric comparison, retaining the original inverse-image opens.
No sheaf transition, cocycle or whole-fiber coefficient is an input.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Motivic _root_.AlgebraicGeometry.Scheme.Intersection

universe u

namespace Motivic.MotivicTest.AffineTorSheafRestriction
open _root_.AlgebraicGeometry.Scheme.Modules.QuasiCoherent.Affine

/-- Naturality uses actual section-ring module maps and the original open inclusion. -/
theorem actualAffineNaturality {X : Scheme.{u}} {U V : X.affineOpens} (h : U ≤ V)
    {M N : ModuleCat.{u} Γ(X, V)} (f : M ⟶ N) :
    (Scheme.Modules.restrictFunctor (X.homOfLE h)).map ((OpenTilde.chartTilde V).map f) ≫
        (OpenTilde.restrictionIso h).hom.app N =
      (OpenTilde.restrictionIso h).hom.app M ≫
        (OpenTilde.chartTilde U).map
          ((ModuleCat.extendScalars
            (X.presheaf.map (homOfLE (show U.1 ≤ V.1 from h)).op).hom).map f) :=
  OpenTilde.restrictionIso_naturality h f

variable {S X Y Z W : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
  {h : Z ⟶ S} {i : W ⟶ S} [IsSeparated g]
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)

/-- The original pair Tor chart sheaf restricts on the actual incidence open. -/
def actualPairSheafRestriction
    {U V : (_root_.AlgebraicGeometry.Scheme.Products.correspondenceIntersectionAmbient f g
        h).affineOpens} (hUV : U ≤ V) (n : ℕ) :
    (Scheme.Modules.restrictFunctor ((F.incidence G).homOfLE
      (((F.incidenceInclusion G) ≫
          _root_.AlgebraicGeometry.Scheme.Products.correspondenceTripleInclusion f g
          h).preimage_mono hUV))).obj
      (closedIntersectionTorChartSheaf (F.supportProductInclusion G)
        (F.incidenceInclusion G) (F.incidenceToSupportProduct G)
        (_root_.AlgebraicGeometry.Scheme.Products.correspondenceTripleInclusion f g h)
            (F.incidence_ambient_isPullback G) V n) ≅
    closedIntersectionTorChartSheaf (F.supportProductInclusion G)
      (F.incidenceInclusion G) (F.incidenceToSupportProduct G)
      (_root_.AlgebraicGeometry.Scheme.Products.correspondenceTripleInclusion f g h)
          (F.incidence_ambient_isPullback G) U n :=
  closedIntersectionTorSheafRestrictionIso _ _ _ _ _ hUV n

/-- The actual first-stage exterior sheaf has its genuine closed-open restriction. -/
def actualExteriorSheafRestriction
    {U V : (_root_.AlgebraicGeometry.Scheme.Products.correspondenceSixfoldAmbient f g h
        i).affineOpens} (hUV : U ≤ V) (n : ℕ) :
    (Scheme.Modules.restrictFunctor ((F.leftIntermediateSupportProduct G H).homOfLE
      (((F.leftIntermediateSupportInclusion G H) ≫
        _root_.AlgebraicGeometry.Scheme.Products.correspondenceFirstDiagonalInclusion f g h
            i).preimage_mono hUV))).obj
      (closedIntersectionTorChartSheaf (F.tripleSupportProductInclusion G H)
        (F.leftIntermediateSupportInclusion G H) (F.leftIntermediateToTripleSupport G H)
        (_root_.AlgebraicGeometry.Scheme.Products.correspondenceFirstDiagonalInclusion f g h i)
        (F.leftIntermediate_ambient_isPullback G H) V n) ≅
    closedIntersectionTorChartSheaf (F.tripleSupportProductInclusion G H)
      (F.leftIntermediateSupportInclusion G H) (F.leftIntermediateToTripleSupport G H)
      (_root_.AlgebraicGeometry.Scheme.Products.correspondenceFirstDiagonalInclusion f g h i)
      (F.leftIntermediate_ambient_isPullback G H) U n :=
  closedIntersectionTorSheafRestrictionIso _ _ _ _ _ hUV n

/-- The smaller actual first-stage sheaf remains genuinely quasi-coherent. -/
theorem actualExteriorTargetQuasicoherent
    (U : (_root_.AlgebraicGeometry.Scheme.Products.correspondenceSixfoldAmbient f g h
        i).affineOpens) (n : ℕ) :
    (closedIntersectionTorChartSheaf (F.tripleSupportProductInclusion G H)
      (F.leftIntermediateSupportInclusion G H) (F.leftIntermediateToTripleSupport G H)
      (_root_.AlgebraicGeometry.Scheme.Products.correspondenceFirstDiagonalInclusion f g h i)
      (F.leftIntermediate_ambient_isPullback G H) U n).IsQuasicoherent :=
  closedIntersectionTorChartSheaf_quasicoherent _ _ _ _ _ _ _

end Motivic.MotivicTest.AffineTorSheafRestriction
