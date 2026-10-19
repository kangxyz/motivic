/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Intersection.ClosedIntersectionTorRestriction
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Associativity.DiagonalAmbient

/-!
# Actual pair and six-factor Tor chart refinements

The original pair and exterior chart coefficients restrict by the constructed
scalar-extension comparison. The actual full section ideals and scalar rings
are retained, and finite generation on the smaller chart is derived from the
original finite-type geometry. No transition or cocycle is assumed.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Motivic _root_.AlgebraicGeometry.Scheme.Intersection

universe u

namespace MotivicTest.ClosedIntersectionTorRestriction

variable {S X Y Z W : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i) [IsSeparated g]

/-- Refinement of the actual pair coefficient uses its original support-section restriction. -/
def actualPairRefinement
    {U V : (_root_.AlgebraicGeometry.Scheme.Products.correspondenceIntersectionAmbient f g
        h).affineOpens} (hUV : U ≤ V) (n : ℕ) :
    (ModuleCat.extendScalars
      (closedIntersectionAffineRestriction
          (_root_.AlgebraicGeometry.Scheme.Products.correspondenceTripleInclusion f g h)
        (F.incidenceInclusion G) hUV)).obj
      (closedIntersectionAffineTor (F.supportProductInclusion G)
        (F.incidenceInclusion G) (F.incidenceToSupportProduct G)
        (_root_.AlgebraicGeometry.Scheme.Products.correspondenceTripleInclusion f g h)
            (F.incidence_ambient_isPullback G) V n) ≅
      closedIntersectionAffineTor (F.supportProductInclusion G)
        (F.incidenceInclusion G) (F.incidenceToSupportProduct G)
        (_root_.AlgebraicGeometry.Scheme.Products.correspondenceTripleInclusion f g h)
            (F.incidence_ambient_isPullback G) U n :=
  closedIntersectionAffineTorRestrictionIso _ _ _ _ _ hUV n

/-- The genuine exterior first-stage refinement has the exact original module endpoints. -/
def actualExteriorRefinement
    {U V : (_root_.AlgebraicGeometry.Scheme.Products.correspondenceSixfoldAmbient f g h
        i).affineOpens} (hUV : U ≤ V) (n : ℕ) :
    (ModuleCat.extendScalars
      (closedIntersectionAffineRestriction
          (_root_.AlgebraicGeometry.Scheme.Products.correspondenceFirstDiagonalInclusion f g h i)
        (F.leftIntermediateSupportInclusion G H) hUV)).obj
      (closedIntersectionAffineTor (F.tripleSupportProductInclusion G H)
        (F.leftIntermediateSupportInclusion G H) (F.leftIntermediateToTripleSupport G H)
        (_root_.AlgebraicGeometry.Scheme.Products.correspondenceFirstDiagonalInclusion f g h i)
        (F.leftIntermediate_ambient_isPullback G H) V n) ≅
      closedIntersectionAffineTor (F.tripleSupportProductInclusion G H)
        (F.leftIntermediateSupportInclusion G H) (F.leftIntermediateToTripleSupport G H)
        (_root_.AlgebraicGeometry.Scheme.Products.correspondenceFirstDiagonalInclusion f g h i)
        (F.leftIntermediate_ambient_isPullback G H) U n :=
  closedIntersectionAffineTorRestrictionIso _ _ _ _ _ hUV n

/-- The actual exterior quotient charts commute with the original support restrictions. -/
theorem actualExteriorRestrictionSquare
    {U V : (_root_.AlgebraicGeometry.Scheme.Products.correspondenceSixfoldAmbient f g h
        i).affineOpens} (hUV : U ≤ V) :
    let a := F.leftIntermediateSupportInclusion G H
    let b := F.leftIntermediateToTripleSupport G H
    let d := _root_.AlgebraicGeometry.Scheme.Products.correspondenceFirstDiagonalInclusion f g h i
    let j := F.tripleSupportProductInclusion G H
    let sq := F.leftIntermediate_ambient_isPullback G H
    (closedIntersectionAffineRestriction d a hUV).comp
        (closedIntersectionAffineQuotientEquiv j a b d sq V).toRingHom =
      (closedIntersectionAffineQuotientEquiv j a b d sq U).toRingHom.comp
        (closedIntersectionSupportQuotientRestriction j d hUV) :=
  closedIntersectionAffineRestriction_square _ _ _ _ _ hUV

/-- The scalar-extended actual exterior coefficient is genuinely finite on the
smaller chart, with Noetherianity derived from the original finite-type maps. -/
theorem actualExteriorRefinementFinite [IsLocallyNoetherian S]
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] [LocallyOfFiniteType h]
    [LocallyOfFiniteType i]
    {U V : (_root_.AlgebraicGeometry.Scheme.Products.correspondenceSixfoldAmbient f g h
        i).affineOpens} (hUV : U ≤ V) (n : ℕ) :
    Module.Finite Γ(F.leftIntermediateSupportProduct G H,
      (F.leftIntermediateAmbientInclusion G H) ⁻¹ᵁ U)
      ((ModuleCat.extendScalars
        (closedIntersectionAffineRestriction
            (_root_.AlgebraicGeometry.Scheme.Products.correspondenceFirstDiagonalInclusion f g h i)
          (F.leftIntermediateSupportInclusion G H) hUV)).obj
        (closedIntersectionAffineTor (F.tripleSupportProductInclusion G H)
          (F.leftIntermediateSupportInclusion G H) (F.leftIntermediateToTripleSupport G H)
          (_root_.AlgebraicGeometry.Scheme.Products.correspondenceFirstDiagonalInclusion f g h i)
          (F.leftIntermediate_ambient_isPullback G H) V n)) := by
  have := _root_.AlgebraicGeometry.Scheme.isLocallyNoetherian_correspondenceSixfoldAmbient f g h i
  exact Module.Finite.of_surjective (actualExteriorRefinement F G H hUV n).inv.hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

end MotivicTest.ClosedIntersectionTorRestriction
