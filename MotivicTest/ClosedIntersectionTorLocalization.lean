/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Intersection.ClosedIntersectionTorLocalization
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Associativity.DiagonalAmbient
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Incidence.IntermediateModules

/-!
# Actual pair and six-factor affine coefficient localization consumers

The actual affine coefficient localizes to the already-defined pair incidence
stalk action. The exterior specialization retains the genuine six-factor
ideals and the actual first-stage stalk map. Its regular diagonal list is
constructed from the original geometry before identifying all homology degrees.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open RingTheory.Sequence
open Motivic
open _root_.AlgebraicGeometry.Scheme.Intersection

universe u

namespace MotivicTest.ClosedIntersectionTorLocalization

variable {S X Y Z W : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i) [IsSeparated g]

/-- The actual pair chart localizes to the existing incidenceTorOnIncidence,
with its original supported-stalk action rather than a new coefficient definition. -/
def actualPairAffineStalkIso [Flat f] [Smooth g] [Flat h]
    (U : (_root_.AlgebraicGeometry.Scheme.Products.correspondenceIntersectionAmbient f g
        h).affineOpens) (w : F.incidence G)
    (hw : F.incidenceAmbientInclusion G w ∈ U.1) (n : ℕ) :
    (ModuleCat.extendScalars
      ((F.incidence G).presheaf.germ ((F.incidenceAmbientInclusion G) ⁻¹ᵁ U) w hw).hom).obj
      (closedIntersectionAffineTor (F.supportProductInclusion G)
        (F.incidenceInclusion G) (F.incidenceToSupportProduct G)
        (_root_.AlgebraicGeometry.Scheme.Products.correspondenceTripleInclusion f g h)
            (F.incidence_ambient_isPullback G) U n) ≅
      F.incidenceTorOnIncidence G w n :=
  closedIntersectionAffineTorStalkIso
      (_root_.AlgebraicGeometry.Scheme.Products.correspondenceTripleInclusion f g h)
    (F.supportProductInclusion G) (F.incidenceInclusion G) (F.incidenceToSupportProduct G)
    (F.incidence_ambient_isPullback G) U w hw n

/-- The actual first-stage exterior coefficient localizes with its full support action. -/
def actualExteriorAffineStalkIso
    (U : (_root_.AlgebraicGeometry.Scheme.Products.correspondenceSixfoldAmbient f g h
        i).affineOpens)
    (w : F.leftIntermediateSupportProduct G H)
    (hw : F.leftIntermediateAmbientInclusion G H w ∈ U.1) (n : ℕ) :=
  closedIntersectionAffineTorStalkIso
      (_root_.AlgebraicGeometry.Scheme.Products.correspondenceFirstDiagonalInclusion f g h i)
    (F.tripleSupportProductInclusion G H) (F.leftIntermediateSupportInclusion G H)
    (F.leftIntermediateToTripleSupport G H) (F.leftIntermediate_ambient_isPullback G H) U w hw n

/-- The tensor source has the literal germ action from the original support section ring. -/
def actualExteriorTensorStalkIso
    (U : (_root_.AlgebraicGeometry.Scheme.Products.correspondenceSixfoldAmbient f g h
        i).affineOpens)
    (w : F.leftIntermediateSupportProduct G H)
    (hw : F.leftIntermediateAmbientInclusion G H w ∈ U.1) (n : ℕ) :=
  closedIntersectionAffineTorTensorStalkIso
      (_root_.AlgebraicGeometry.Scheme.Products.correspondenceFirstDiagonalInclusion f g h i)
    (F.tripleSupportProductInclusion G H) (F.leftIntermediateSupportInclusion G H)
    (F.leftIntermediateToTripleSupport G H) (F.leftIntermediate_ambient_isPullback G H) U w hw n

/-- The actual first-stage scalar square commutes on the full quotient, not just residue fields. -/
theorem actualExteriorGermSquare
    (U : (_root_.AlgebraicGeometry.Scheme.Products.correspondenceSixfoldAmbient f g h
        i).affineOpens)
    (w : F.leftIntermediateSupportProduct G H)
    (hw : F.leftIntermediateAmbientInclusion G H w ∈ U.1) :
    let a := F.leftIntermediateSupportInclusion G H
    let b := F.leftIntermediateToTripleSupport G H
    let d := _root_.AlgebraicGeometry.Scheme.Products.correspondenceFirstDiagonalInclusion f g h i
    let j := F.tripleSupportProductInclusion G H
    let sq := F.leftIntermediate_ambient_isPullback G H
    ((F.leftIntermediateSupportProduct G H).presheaf.germ ((a ≫ d) ⁻¹ᵁ U) w hw).hom.comp
        (closedIntersectionAffineQuotientEquiv j a b d sq U).toRingHom =
      (affineIntersectionStalkQuotientEquiv d j a b sq U w hw).toRingHom.comp
        (_root_.ModuleCat.TorComparison.supportQuotientMapSup
          ((_root_.AlgebraicGeometry.Scheme.Products.correspondenceSixfoldAmbient f g h
              i).presheaf.germ U.1 ((a ≫ d) w) hw).hom
          (d.ker.ideal U) (j.ker.ideal U)) :=
  affineIntersectionQuotient_germ_square _ _ _ _ _ _ _ _

/-- The actual regular diagonal list is constructed, and the original exterior
homology is recovered from the actual affine coefficient in every degree. -/
theorem actualExteriorAffineKoszul [Flat f] [Smooth g] [Flat h] [Flat i]
    (U : (_root_.AlgebraicGeometry.Scheme.Products.correspondenceSixfoldAmbient f g h
        i).affineOpens)
    (w : F.leftIntermediateSupportProduct G H)
    (hw : F.leftIntermediateAmbientInclusion G H w ∈ U.1) :
    let a := F.leftIntermediateSupportInclusion G H
    let b := F.leftIntermediateToTripleSupport G H
    let d := _root_.AlgebraicGeometry.Scheme.Products.correspondenceFirstDiagonalInclusion f g h i
    let j := F.tripleSupportProductInclusion G H
    let sq := F.leftIntermediate_ambient_isPullback G H
    let hp := point_eq a b d j sq w
    ∃ s : List (ambientStalk d (a w)), IsRegular (ambientStalk d (a w)) s ∧
      RingHom.ker (d.stalkMap (a w)).hom = Ideal.ofList s ∧
      ∀ n : ℕ, Nonempty
        ((ModuleCat.restrictScalars ((a ≫ d).stalkMap w).hom).obj
          ((ModuleCat.extendScalars
            ((F.leftIntermediateSupportProduct G H).presheaf.germ
              ((a ≫ d) ⁻¹ᵁ U) w hw).hom).obj
            (closedIntersectionAffineTor j a b d sq U n)) ≅
          (_root_.ChainComplex.Koszul.coefficientComplex
            (coefficientStalkModule d (a w) j (b w) hp) s).homology n) := by
  dsimp only
  obtain ⟨s, hs, hker⟩ :=
      _root_.AlgebraicGeometry.Scheme.Products.exists_regular_kernel_correspondenceFirstDiagonal f g
      h i
    (F.leftIntermediateSupportInclusion G H w)
  exact ⟨s, hs, hker, fun n => ⟨closedIntersectionAffineTorKoszulStalkIso _ _ _ _ _ U w hw
    s hker hs n⟩⟩

end MotivicTest.ClosedIntersectionTorLocalization
