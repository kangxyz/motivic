/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Intersection.ClosedIntersectionTorChartStalk
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Noetherian
public import Motivic.AlgebraicGeometry.Correspondences.Noetherian
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Incidence.IntermediateModules
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Associativity.DiagonalAmbient

/-!
# Actual pair and six-factor Tor chart-sheaf stalk consumers

These comparisons begin with actual stalks of the constructed chart sheaves,
use the original inclusion maps, and end at the existing geometric supported
Tor modules. No stalk comparison or target module is supplied as a hypothesis.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Motivic _root_.AlgebraicGeometry.Scheme.Intersection

universe u

namespace MotivicTest.ClosedIntersectionTorChartStalk
open _root_.AlgebraicGeometry.Scheme (SmoothSite)

variable {S X Y Z W : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i) [IsSeparated g]

/-- The actual chart-sheaf stalk is the original pair incidence Tor module. -/
def actualPairChartStalkIso [Flat f] [Smooth g] [Flat h]
    (U : (_root_.AlgebraicGeometry.Scheme.Products.correspondenceIntersectionAmbient f g
        h).affineOpens) (w : F.incidence G)
    (hw : F.incidenceAmbientInclusion G w ∈ U.1) (n : ℕ) :
    closedIntersectionTorChartStalk
        (_root_.AlgebraicGeometry.Scheme.Products.correspondenceTripleInclusion f g h)
      (F.supportProductInclusion G) (F.incidenceInclusion G) (F.incidenceToSupportProduct G)
      (F.incidence_ambient_isPullback G) U w hw n ≅ F.incidenceTorOnIncidence G w n :=
  closedIntersectionTorChartStalkIso
      (_root_.AlgebraicGeometry.Scheme.Products.correspondenceTripleInclusion f g h)
    (F.supportProductInclusion G) (F.incidenceInclusion G) (F.incidenceToSupportProduct G)
    (F.incidence_ambient_isPullback G) U w hw n

/-- The actual six-factor first-stage sheaf stalk has the original full support action. -/
def actualExteriorChartStalkIso
    (U : (_root_.AlgebraicGeometry.Scheme.Products.correspondenceSixfoldAmbient f g h
        i).affineOpens)
    (w : F.leftIntermediateSupportProduct G H)
    (hw : F.leftIntermediateAmbientInclusion G H w ∈ U.1) (n : ℕ) :=
  closedIntersectionTorChartStalkIso
      (_root_.AlgebraicGeometry.Scheme.Products.correspondenceFirstDiagonalInclusion f g h i)
    (F.tripleSupportProductInclusion G H) (F.leftIntermediateSupportInclusion G H)
    (F.leftIntermediateToTripleSupport G H) (F.leftIntermediate_ambient_isPullback G H) U w hw n

/-- Finite generation of the actual pair chart-sheaf stalk follows from the
original finite-type geometry over a locally Noetherian base. -/
theorem actualPairChartStalk_finite [IsLocallyNoetherian S]
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] [LocallyOfFiniteType h]
    (U : (_root_.AlgebraicGeometry.Scheme.Products.correspondenceIntersectionAmbient f g
        h).affineOpens) (w : F.incidence G)
    (hw : F.incidenceAmbientInclusion G w ∈ U.1) (n : ℕ) :
    Module.Finite ((F.incidence G).presheaf.stalk w)
      (closedIntersectionTorChartStalk
          (_root_.AlgebraicGeometry.Scheme.Products.correspondenceTripleInclusion f g h)
        (F.supportProductInclusion G) (F.incidenceInclusion G) (F.incidenceToSupportProduct G)
        (F.incidence_ambient_isPullback G) U w hw n) := by
  have := isLocallyNoetherian_correspondenceIntersectionAmbient f g h
  infer_instance

/-- The actual six-factor first-stage chart stalk is finite without a dimension,
integrality, generic-point, or nonempty hypothesis. -/
theorem actualExteriorChartStalk_finite [IsLocallyNoetherian S]
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] [LocallyOfFiniteType h]
    [LocallyOfFiniteType i]
    (U : (_root_.AlgebraicGeometry.Scheme.Products.correspondenceSixfoldAmbient f g h
        i).affineOpens)
    (w : F.leftIntermediateSupportProduct G H)
    (hw : F.leftIntermediateAmbientInclusion G H w ∈ U.1) (n : ℕ) :
    Module.Finite ((F.leftIntermediateSupportProduct G H).presheaf.stalk w)
      (closedIntersectionTorChartStalk
          (_root_.AlgebraicGeometry.Scheme.Products.correspondenceFirstDiagonalInclusion f g h i)
        (F.tripleSupportProductInclusion G H) (F.leftIntermediateSupportInclusion G H)
        (F.leftIntermediateToTripleSupport G H) (F.leftIntermediate_ambient_isPullback G H)
        U w hw n) := by
  have := _root_.AlgebraicGeometry.Scheme.isLocallyNoetherian_correspondenceSixfoldAmbient f g h i
  infer_instance

/-- Original smooth-site objects over every field instantiate the finite actual
first-stage chart-sheaf stalk with no additional ambient finiteness premise. -/
theorem actualSmoothExteriorChartStalk_finite (K : Type u) [Field K]
    (X Y Z W : SmoothSite (Spec (.of K)))
    (F : FiniteCorrespondenceGenerator X.hom Y.hom)
    (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
    (H : FiniteCorrespondenceGenerator Z.hom W.hom)
    (U : (_root_.AlgebraicGeometry.Scheme.Products.correspondenceSixfoldAmbient X.hom Y.hom Z.hom
        W.hom).affineOpens)
    (w : F.leftIntermediateSupportProduct G H)
    (hw : F.leftIntermediateAmbientInclusion G H w ∈ U.1) (n : ℕ) :
    Module.Finite ((F.leftIntermediateSupportProduct G H).presheaf.stalk w)
      (closedIntersectionTorChartStalk
        (_root_.AlgebraicGeometry.Scheme.Products.correspondenceFirstDiagonalInclusion X.hom Y.hom
            Z.hom W.hom)
        (F.tripleSupportProductInclusion G H) (F.leftIntermediateSupportInclusion G H)
        (F.leftIntermediateToTripleSupport G H) (F.leftIntermediate_ambient_isPullback G H)
        U w hw n) :=
  actualExteriorChartStalk_finite (S := Spec (.of K)) F G H U w hw n

end MotivicTest.ClosedIntersectionTorChartStalk
