/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Intersection.ClosedIntersectionTorSheafRestrictionCoherence
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Associativity.DiagonalAmbient

/-!
# Actual affine tilde and Tor chart-sheaf cocycles

The original pair and six-factor chart-sheaf transitions obey the genuine
geometric unit and composition equations. Arbitrary coordinate modules also
consume the canonical affine-open tilde coherence.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Motivic _root_.AlgebraicGeometry.Scheme.Intersection

universe u

namespace Motivic.MotivicTest.AffineTorSheafCoherence
open _root_.AlgebraicGeometry.Scheme.Modules.QuasiCoherent.Affine

/-- The actual affine tilde identity is the geometric unitor on arbitrary modules. -/
theorem actualAffineIdentity {X : Scheme.{u}} (U : X.affineOpens)
    (M : ModuleCat.{u} Γ(X, U)) :
    (OpenTilde.restrictionIso (show U ≤ U from le_rfl)).hom.app M ≫
      (OpenTilde.chartTilde U).map (OpenTilde.scalarIdentityIso U M).hom =
    (OpenTilde.openIdentityIso (X := X) U.1).hom.app
      ((OpenTilde.chartTilde U).obj M) :=
  OpenTilde.restrictionIso_hom_refl U M

/-- Actual affine tilde composition keeps both genuine associators. -/
theorem actualAffineComposition {X : Scheme.{u}} {U V L : X.affineOpens}
    (h : U ≤ V) (k : V ≤ L) (M : ModuleCat.{u} Γ(X, L)) :
    (OpenTilde.openCompositionIso (X := X) h k).hom.app
        ((OpenTilde.chartTilde L).obj M) ≫
      (Scheme.Modules.restrictFunctor (X.homOfLE h)).map
        ((OpenTilde.restrictionIso k).hom.app M) ≫
      (OpenTilde.restrictionIso h).hom.app
        ((ModuleCat.extendScalars (OpenTilde.sectionRestriction k).hom).obj M) =
    (OpenTilde.restrictionIso (h.trans k)).hom.app M ≫
      (OpenTilde.chartTilde U).map (OpenTilde.scalarCompositionIso h k M).hom :=
  OpenTilde.restrictionIso_hom_comp h k M

variable {S X Y Z W : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i) [IsSeparated g]

/-- The original pair sheaf identity is the actual open-restriction unitor. -/
theorem actualPairIdentity (U :
    (_root_.AlgebraicGeometry.Scheme.Products.correspondenceIntersectionAmbient f g h).affineOpens)
    (n : ℕ) :
    let d := _root_.AlgebraicGeometry.Scheme.Products.correspondenceTripleInclusion f g h
    let j := F.supportProductInclusion G
    let a := F.incidenceInclusion G
    let b := F.incidenceToSupportProduct G
    let sq := F.incidence_ambient_isPullback G
    (closedIntersectionTorSheafRestrictionIso j d a b sq (show U ≤ U from le_rfl) n).hom =
      (OpenTilde.openIdentityIso (X := F.incidence G)
        (closedIntersectionAffineOpen j a b d sq U).1).hom.app
          (closedIntersectionTorChartSheaf j a b d sq U n) :=
  closedIntersectionTorSheafRestrictionIso_hom_refl _ _ _ _ _ U n

/-- The two original pair chart-sheaf transitions equal direct refinement. -/
theorem actualPairComposition {U V L :
    (_root_.AlgebraicGeometry.Scheme.Products.correspondenceIntersectionAmbient f g h).affineOpens}
    (hUV : U ≤ V) (hVL : V ≤ L) (n : ℕ) :
    let d := _root_.AlgebraicGeometry.Scheme.Products.correspondenceTripleInclusion f g h
    let j := F.supportProductInclusion G
    let a := F.incidenceInclusion G
    let b := F.incidenceToSupportProduct G
    let sq := F.incidence_ambient_isPullback G
    (OpenTilde.openCompositionIso (X := F.incidence G)
      ((a ≫ d).preimage_mono hUV) ((a ≫ d).preimage_mono hVL)).hom.app
        (closedIntersectionTorChartSheaf j a b d sq L n) ≫
      (Scheme.Modules.restrictFunctor ((F.incidence G).homOfLE
        ((a ≫ d).preimage_mono hUV))).map
          (closedIntersectionTorSheafRestrictionIso j d a b sq hVL n).hom ≫
      (closedIntersectionTorSheafRestrictionIso j d a b sq hUV n).hom =
    (closedIntersectionTorSheafRestrictionIso j d a b sq (hUV.trans hVL) n).hom :=
  closedIntersectionTorSheafRestrictionIso_hom_comp _ _ _ _ _ hUV hVL n

/-- The original exterior sheaf identity is the actual open-restriction unitor. -/
theorem actualExteriorIdentity (U :
    (_root_.AlgebraicGeometry.Scheme.Products.correspondenceSixfoldAmbient f g h i).affineOpens) (n
    : ℕ) :
    let d := _root_.AlgebraicGeometry.Scheme.Products.correspondenceFirstDiagonalInclusion f g h i
    let j := F.tripleSupportProductInclusion G H
    let a := F.leftIntermediateSupportInclusion G H
    let b := F.leftIntermediateToTripleSupport G H
    let sq := F.leftIntermediate_ambient_isPullback G H
    (closedIntersectionTorSheafRestrictionIso j d a b sq (show U ≤ U from le_rfl) n).hom =
      (OpenTilde.openIdentityIso (X := F.leftIntermediateSupportProduct G H)
        (closedIntersectionAffineOpen j a b d sq U).1).hom.app
          (closedIntersectionTorChartSheaf j a b d sq U n) :=
  closedIntersectionTorSheafRestrictionIso_hom_refl _ _ _ _ _ U n

/-- The two original exterior chart-sheaf transitions equal direct refinement. -/
theorem actualExteriorComposition {U V L :
    (_root_.AlgebraicGeometry.Scheme.Products.correspondenceSixfoldAmbient f g h i).affineOpens}
    (hUV : U ≤ V) (hVL : V ≤ L) (n : ℕ) :
    let d := _root_.AlgebraicGeometry.Scheme.Products.correspondenceFirstDiagonalInclusion f g h i
    let j := F.tripleSupportProductInclusion G H
    let a := F.leftIntermediateSupportInclusion G H
    let b := F.leftIntermediateToTripleSupport G H
    let sq := F.leftIntermediate_ambient_isPullback G H
    (OpenTilde.openCompositionIso (X := F.leftIntermediateSupportProduct G H)
      ((a ≫ d).preimage_mono hUV) ((a ≫ d).preimage_mono hVL)).hom.app
        (closedIntersectionTorChartSheaf j a b d sq L n) ≫
      (Scheme.Modules.restrictFunctor ((F.leftIntermediateSupportProduct G H).homOfLE
        ((a ≫ d).preimage_mono hUV))).map
          (closedIntersectionTorSheafRestrictionIso j d a b sq hVL n).hom ≫
      (closedIntersectionTorSheafRestrictionIso j d a b sq hUV n).hom =
    (closedIntersectionTorSheafRestrictionIso j d a b sq (hUV.trans hVL) n).hom :=
  closedIntersectionTorSheafRestrictionIso_hom_comp _ _ _ _ _ hUV hVL n

end Motivic.MotivicTest.AffineTorSheafCoherence
