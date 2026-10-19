/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Graph.Stalks.Right

/-!
# Consumers of exact incidence graph-stalk scalar transport

The actual right identity and right graph products have the stated ring
isomorphisms. The two paths carry every individual diagonal element to the
same coefficient element. The last consumer checks the exact image-list
interpretation of coefficient regularity, including the actual scalar action.
-/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme.Products (graphMiddlePair)
open _root_.AlgebraicGeometry.Scheme.Diagonal (baseChangeStalkMap)
open _root_.AlgebraicGeometry.Scheme.Intersection (coefficientStalkMap
  coefficientStalkModule_isWeaklyRegular_iff point_eq)
open _root_.AlgebraicGeometry.Scheme.Products (correspondenceTripleInclusion
  correspondenceTripleMiddle correspondenceTriple_isPullback)
open _root_.AlgebraicGeometry.Scheme.StalkTransport (pointedMap)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingTheory.Sequence Motivic

universe u

namespace MotivicTest.RightGraphStalk

variable {S X Y Z : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S}
  (A : FiniteCorrespondenceGenerator f g)

/-- The actual identity coefficient stalk is the graph-product stalk as a ring. -/
def identityCoefficientStalk [IsIntegral Y] [IsSeparated g]
    (w : A.incidence (identityGenerator g)) :
    (pullback (A.targetProjection ≫ g) g).presheaf.stalk
        (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph A.targetProjection g
          (A.incidenceFst (identityGenerator g) w)) ≅
      (A.supportProduct (identityGenerator g)).presheaf.stalk
        (A.incidenceToSupportProduct (identityGenerator g) w) :=
  A.incidenceGraphStalkIso (identityGenerator g) w

/-- The same ring comparison applies to an arbitrary genuine graph generator. -/
def graphCoefficientStalk (ψ : Y ⟶ Z) (hw : ψ ≫ h = g)
    [IsIntegral Y] [IsSeparated h] (w : A.incidence (graphGeneratorOver ψ hw)) :
    (pullback (A.targetProjection ≫ g) g).presheaf.stalk
        (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph A.targetProjection g
          (A.incidenceFst (graphGeneratorOver ψ hw) w)) ≅
      (A.supportProduct (graphGeneratorOver ψ hw)).presheaf.stalk
        (A.incidenceToSupportProduct (graphGeneratorOver ψ hw) w) :=
  A.incidenceGraphStalkIso (graphGeneratorOver ψ hw) w

/-- Every diagonal element follows exactly the same actual coefficient scalar path. -/
theorem actual_scalar_element
    (B : FiniteCorrespondenceGenerator g h) [IsIso B.projection] (w : A.incidence B)
    (r : (pullback g g).presheaf.stalk
      (pullback.diagonal g
        (correspondenceTripleMiddle f g h (A.incidenceInclusion B w)))) :
    coefficientStalkMap
        (correspondenceTripleInclusion f g h) (A.incidenceInclusion B w)
        (A.supportProductInclusion B) (A.incidenceToSupportProduct B w)
        (point_eq _ _ _ _ (A.incidence_ambient_isPullback B) w)
      (baseChangeStalkMap (correspondenceTriple_isPullback f g h)
        (A.incidenceInclusion B w) r) =
    (A.incidenceGraphStalkIso B w).hom
      (pointedMap (graphMiddlePair A.targetProjection g)
        (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph A.targetProjection g
          (A.incidenceFst B w))
        (pullback.diagonal g
          (correspondenceTripleMiddle f g h (A.incidenceInclusion B w)))
        (A.incidenceGraphMiddlePoint_eq B w) r) :=
  ConcreteCategory.congr_hom (A.incidenceDiagonalStalkMap_comp B w) r

/-- The module test uses the actual coefficient map, retaining the full stalk ring. -/
theorem coefficient_regularity_iff_actual_image
    (B : FiniteCorrespondenceGenerator g h) (w : A.incidence B)
    (rs : List (A.incidenceAmbientStalk B w)) :
    IsWeaklyRegular (A.incidenceSupportStalkModule B w) rs ↔
      IsWeaklyRegular ((A.supportProduct B).presheaf.stalk (A.incidenceToSupportProduct B w))
        (rs.map (coefficientStalkMap
          (correspondenceTripleInclusion f g h) (A.incidenceInclusion B w)
          (A.supportProductInclusion B) (A.incidenceToSupportProduct B w)
          (point_eq _ _ _ _ (A.incidence_ambient_isPullback B) w)).hom) :=
  coefficientStalkModule_isWeaklyRegular_iff _ _ _ _ _ _

end MotivicTest.RightGraphStalk
