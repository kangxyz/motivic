/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Intersection.ClosedIntersectionTorRestrictionCoherence
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Associativity.DiagonalAmbient

/-!
# Coherent actual pair and six-factor Tor chart refinements

The identity and two-step refinement equations below concern the original
pair and exterior chart-module isomorphisms, their literal whole inverse-image
section maps, and the genuine scalar unitors and associators.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Motivic _root_.AlgebraicGeometry.Scheme.Intersection

universe u

namespace MotivicTest.ClosedIntersectionTorRestrictionCoherence

variable {S X Y Z W : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i) [IsSeparated g]

/-- The original pair chart identity is the actual scalar-extension unitor. -/
theorem actualPairIdentity (U :
    (_root_.AlgebraicGeometry.Scheme.Products.correspondenceIntersectionAmbient f g h).affineOpens)
    (n : ℕ) :
    let d := _root_.AlgebraicGeometry.Scheme.Products.correspondenceTripleInclusion f g h
    let j := F.supportProductInclusion G
    let a := F.incidenceInclusion G
    let b := F.incidenceToSupportProduct G
    let sq := F.incidence_ambient_isPullback G
    let M := closedIntersectionAffineTor j a b d sq U n
    (closedIntersectionAffineTorRestrictionIso j d a b sq (show U ≤ U from le_rfl) n).hom =
      (eqToIso (congrArg (fun q => (ModuleCat.extendScalars q).obj M)
        (closedIntersectionAffineRestriction_refl d a U))).hom ≫
      (ModuleCat.extendScalarsId _).hom.app M :=
  closedIntersectionAffineTorRestrictionIso_hom_refl _ _ _ _ _ U n

/-- The original pair chart transitions obey actual two-step scalar composition. -/
theorem actualPairComposition {U V L :
    (_root_.AlgebraicGeometry.Scheme.Products.correspondenceIntersectionAmbient f g h).affineOpens}
    (hUV : U ≤ V) (hVL : V ≤ L) (n : ℕ) :
    let d := _root_.AlgebraicGeometry.Scheme.Products.correspondenceTripleInclusion f g h
    let j := F.supportProductInclusion G
    let a := F.incidenceInclusion G
    let b := F.incidenceToSupportProduct G
    let sq := F.incidence_ambient_isPullback G
    let M := closedIntersectionAffineTor j a b d sq L n
    (ModuleCat.extendScalarsComp (closedIntersectionAffineRestriction d a hVL)
      (closedIntersectionAffineRestriction d a hUV)).hom.app M ≫
      (ModuleCat.extendScalars (closedIntersectionAffineRestriction d a hUV)).map
        (closedIntersectionAffineTorRestrictionIso j d a b sq hVL n).hom ≫
      (closedIntersectionAffineTorRestrictionIso j d a b sq hUV n).hom =
    (eqToIso (congrArg (fun q => (ModuleCat.extendScalars q).obj M)
      (closedIntersectionAffineRestriction_comp d a hUV hVL))).hom ≫
      (closedIntersectionAffineTorRestrictionIso j d a b sq (hUV.trans hVL) n).hom :=
  closedIntersectionAffineTorRestrictionIso_hom_comp _ _ _ _ _ hUV hVL n

/-- The original exterior chart identity is the actual scalar-extension unitor. -/
theorem actualExteriorIdentity (U :
    (_root_.AlgebraicGeometry.Scheme.Products.correspondenceSixfoldAmbient f g h i).affineOpens) (n
    : ℕ) :
    let d := _root_.AlgebraicGeometry.Scheme.Products.correspondenceFirstDiagonalInclusion f g h i
    let j := F.tripleSupportProductInclusion G H
    let a := F.leftIntermediateSupportInclusion G H
    let b := F.leftIntermediateToTripleSupport G H
    let sq := F.leftIntermediate_ambient_isPullback G H
    let M := closedIntersectionAffineTor j a b d sq U n
    (closedIntersectionAffineTorRestrictionIso j d a b sq (show U ≤ U from le_rfl) n).hom =
      (eqToIso (congrArg (fun q => (ModuleCat.extendScalars q).obj M)
        (closedIntersectionAffineRestriction_refl d a U))).hom ≫
      (ModuleCat.extendScalarsId _).hom.app M :=
  closedIntersectionAffineTorRestrictionIso_hom_refl _ _ _ _ _ U n

/-- The original exterior chart transitions obey actual two-step scalar composition. -/
theorem actualExteriorComposition {U V L :
    (_root_.AlgebraicGeometry.Scheme.Products.correspondenceSixfoldAmbient f g h i).affineOpens}
    (hUV : U ≤ V) (hVL : V ≤ L) (n : ℕ) :
    let d := _root_.AlgebraicGeometry.Scheme.Products.correspondenceFirstDiagonalInclusion f g h i
    let j := F.tripleSupportProductInclusion G H
    let a := F.leftIntermediateSupportInclusion G H
    let b := F.leftIntermediateToTripleSupport G H
    let sq := F.leftIntermediate_ambient_isPullback G H
    let M := closedIntersectionAffineTor j a b d sq L n
    (ModuleCat.extendScalarsComp (closedIntersectionAffineRestriction d a hVL)
      (closedIntersectionAffineRestriction d a hUV)).hom.app M ≫
      (ModuleCat.extendScalars (closedIntersectionAffineRestriction d a hUV)).map
        (closedIntersectionAffineTorRestrictionIso j d a b sq hVL n).hom ≫
      (closedIntersectionAffineTorRestrictionIso j d a b sq hUV n).hom =
    (eqToIso (congrArg (fun q => (ModuleCat.extendScalars q).obj M)
      (closedIntersectionAffineRestriction_comp d a hUV hVL))).hom ≫
      (closedIntersectionAffineTorRestrictionIso j d a b sq (hUV.trans hVL) n).hom :=
  closedIntersectionAffineTorRestrictionIso_hom_comp _ _ _ _ _ hUV hVL n

end MotivicTest.ClosedIntersectionTorRestrictionCoherence
