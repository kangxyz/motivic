/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Exterior.RightPairStalks
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Noetherian
public import Motivic.AlgebraicGeometry.Correspondences.Noetherian

/-!
# Actual arbitrary-field right exterior stalk consumers

The first support is an arbitrary finite-correspondence generator, with no
regularity, normality, or flatness over Y supplied. Flatness of the literal
exterior maps is obtained over the base field. The consumers retain the original
second diagonal, all three supports, the actual G,H incidence, and the original
closed-fiber quotient in every Tor degree.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open _root_.AlgebraicGeometry.Scheme.Intersection (closedIntersectionSupportedStalkTor)
open _root_.AlgebraicGeometry.Scheme.Products (correspondenceSecondAmbientInclusion
  correspondenceTripleInclusion)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

namespace MotivicTest.RightExteriorPairStalks

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

local instance rightExterior_factorFlat : Flat (F.targetProjection ≫ Y.hom) := by
  let : Subsingleton (Spec (.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  let : IsIntegral (Spec (.of k)) := inferInstance
  exact Flat.instOfSubsingletonCarrierCarrierCommRingCatOfIsIntegral
    (Y := Spec (.of k)) (F.targetProjection ≫ Y.hom)

/-- The original coefficient projection is flat without flatness of F over Y. -/
theorem actualCoefficientProjectionFlat : Flat (F.rightExteriorCoefficientProjection G H) :=
  inferInstance

/-- The direct whole-incidence projection is an exterior base change over k. -/
theorem actualPairProjectionFlat : Flat (F.rightExteriorPairProjection G H) :=
  inferInstance

/-- The original six-factor second diagonal is pulled back from the original
G,H diagonal through the literal right ambient projection. -/
theorem actualRightDiagonalCartesian :
    IsPullback (correspondenceSecondDiagonalRightPairProjection X.hom Y.hom Z.hom W.hom)
      (correspondenceSecondAmbientInclusion X.hom Y.hom Z.hom W.hom)
      (correspondenceTripleInclusion Y.hom Z.hom W.hom)
      (correspondenceSixfoldRightPairProjection X.hom Y.hom Z.hom W.hom) :=
  correspondenceSecondDiagonal_pair_isPullback X.hom Y.hom Z.hom W.hom

/-- The support Cartesian square uses the full original incidence and product. -/
theorem actualRightIncidenceCartesian :
    IsPullback (F.rightExteriorPairProjection G H)
      (F.rightIntermediateToTripleSupport G H) (G.incidenceToSupportProduct H)
      (F.rightExteriorCoefficientProjection G H) :=
  F.rightExteriorIncidence_pair_isPullback G H

/-- Both coefficient-stalk routes come from the actual original scheme square. -/
theorem actualCoefficientSquare :
    F.rightExteriorCoefficientProjection G H ≫ G.supportProductInclusion H =
      F.tripleSupportProductInclusion G H ≫
        correspondenceSixfoldRightPairProjection X.hom Y.hom Z.hom W.hom :=
  F.rightExteriorCoefficientProjection_inclusion G H

/-- Every genuine right-stage generic point has an original G,H pair generic. -/
theorem actualOriginalPairGeneric (w : F.rightIntermediateSupportProduct G H)
    (hw : w ∈ genericPoints (F.rightIntermediateSupportProduct G H)) :
    F.rightExteriorPairProjection G H w ∈ genericPoints (G.incidence H) :=
  F.rightExteriorPairProjection_mem_genericPoints G H w hw

/-- The original supported right Tor in any degree retains the true quotient
fiber, rather than replacing its possibly nonreduced length by one. -/
theorem actualRightSupportedMultiplicity (w : F.rightIntermediateSupportProduct G H) (n : ℕ) :
    Module.length ((F.rightIntermediateSupportProduct G H).presheaf.stalk w)
        (closedIntersectionSupportedStalkTor
          (correspondenceSecondAmbientInclusion X.hom Y.hom Z.hom W.hom)
          (F.tripleSupportProductInclusion G H)
          (F.rightIntermediateSupportInclusion G H) (F.rightIntermediateToTripleSupport G H)
          (F.rightIntermediate_ambient_isPullback G H) w n) =
      Module.length (G.incidenceAmbientStalk H (F.rightExteriorPairProjection G H w))
        (G.incidenceTor H (F.rightExteriorPairProjection G H w) n) *
          Module.length ((F.rightIntermediateSupportProduct G H).presheaf.stalk w)
            (((F.rightIntermediateSupportProduct G H).presheaf.stalk w) ⧸
              (IsLocalRing.maximalIdeal
                ((G.incidence H).presheaf.stalk (F.rightExteriorPairProjection G H w))).map
                  ((F.rightExteriorPairProjection G H).stalkMap w).hom) :=
  F.rightExteriorSupportedTor_length G H w n

end MotivicTest.RightExteriorPairStalks
