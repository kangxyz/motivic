/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.IncidenceTor
public import Motivic.AlgebraicGeometry.Correspondences.GraphIntersectionDiagram
public import Motivic.AlgebraicGeometry.Intersection.CoefficientStalkTransport

/-!
# Actual graph-stalk scalars for incidence

When the second support has isomorphic source projection, its product with
the first support is the actual graph ambient product. The induced ring
isomorphism of actual stalks intertwines the two literal scalar maps from the
same diagonal stalk. Thus regularity of a specific diagonal list on the graph
stalk implies weak regularity of that identical list, after flat ambient
transport, on the actual incidence coefficient module. This adapter does not
assume flatness of the first support target map or select another equation list.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingTheory.Sequence

universe u

namespace Motivic.FiniteCorrespondenceGenerator

section Stalks

variable {S X Y Z : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S}
  (A : FiniteCorrespondenceGenerator f g) (B : FiniteCorrespondenceGenerator g h)

/-- The actual middle point of the incidence embedding is the first support target. -/
theorem incidenceTripleMiddle_apply (w : A.incidence B) :
    correspondenceTripleMiddle f g h (A.incidenceInclusion B w) =
      A.targetProjection (A.incidenceFst B w) := by
  change (A.incidenceInclusion B ≫ correspondenceTripleMiddle f g h) w = _
  have hm : A.incidenceInclusion B ≫ correspondenceTripleMiddle f g h =
      A.incidenceFst B ≫ A.targetProjection := by
    simp only [correspondenceTripleMiddle, incidenceInclusion_fst_assoc]
  rw [hm]
  rfl

/-- The actual graph point is the image of the support-product incidence point. -/
theorem incidenceGraphPoint_eq (w : A.incidence B) :
    correspondenceGraph A.targetProjection g (A.incidenceFst B w) =
      A.supportProductToGraphProduct B (A.incidenceToSupportProduct B w) :=
  (congrArg (fun q => q w) (A.incidenceToSupportProduct_graph B)).symm

/-- The diagonal and graph middle points are equal, using the actual incidence point. -/
theorem incidenceGraphMiddlePoint_eq (w : A.incidence B) :
    pullback.diagonal g
        (correspondenceTripleMiddle f g h (A.incidenceInclusion B w)) =
      graphMiddlePair A.targetProjection g
        (correspondenceGraph A.targetProjection g (A.incidenceFst B w)) := by
  rw [A.incidenceTripleMiddle_apply B w]
  exact (congrArg (fun q => q (A.incidenceFst B w))
    (correspondenceGraph_middlePair A.targetProjection g)).symm

/-- The actual graph-product stalk is the support-product stalk by an actual ring isomorphism. -/
noncomputable def incidenceGraphStalkIso [IsIso B.projection] (w : A.incidence B) :
    (pullback (A.targetProjection ≫ g) g).presheaf.stalk
        (correspondenceGraph A.targetProjection g (A.incidenceFst B w)) ≅
      (A.supportProduct B).presheaf.stalk (A.incidenceToSupportProduct B w) :=
  asIso (StalkTransport.pointedMap (A.supportProductToGraphProduct B)
    (A.incidenceToSupportProduct B w)
    (correspondenceGraph A.targetProjection g (A.incidenceFst B w))
    (A.incidenceGraphPoint_eq B w))

set_option backward.isDefEq.respectTransparency false in
/-- The two actual paths from the same diagonal stalk to the coefficient stalk agree. -/
theorem incidenceDiagonalStalkMap_comp [IsIso B.projection] (w : A.incidence B) :
    Diagonal.baseChangeStalkMap (correspondenceTriple_isPullback f g h)
        (A.incidenceInclusion B w) ≫
      Intersection.coefficientStalkMap
        (correspondenceTripleInclusion f g h) (A.incidenceInclusion B w)
        (A.supportProductInclusion B) (A.incidenceToSupportProduct B w)
        (Intersection.point_eq _ _ _ _ (A.incidence_ambient_isPullback B) w) =
    StalkTransport.pointedMap (graphMiddlePair A.targetProjection g)
        (correspondenceGraph A.targetProjection g (A.incidenceFst B w))
        (pullback.diagonal g
          (correspondenceTripleMiddle f g h (A.incidenceInclusion B w)))
        (A.incidenceGraphMiddlePoint_eq B w) ≫
      (A.incidenceGraphStalkIso B w).hom := by
  change StalkTransport.pointedMap (correspondenceMiddlePair f g h) _ _
      (congrArg (fun q => q (A.incidenceInclusion B w))
        (correspondenceTriple_isPullback f g h).w) ≫
      StalkTransport.pointedMap (A.supportProductInclusion B) _ _
        (Intersection.point_eq _ _ _ _ (A.incidence_ambient_isPullback B) w) =
    StalkTransport.pointedMap (graphMiddlePair A.targetProjection g) _ _
        (A.incidenceGraphMiddlePoint_eq B w) ≫
      StalkTransport.pointedMap (A.supportProductToGraphProduct B) _ _
        (A.incidenceGraphPoint_eq B w)
  rw [StalkTransport.pointedMap_comp, StalkTransport.pointedMap_comp]
  exact StalkTransport.pointedMap_congr _ _ (A.supportProductInclusion_middlePair B) _ _ _ _

/-- Regularity of a diagonal list in the actual graph stalk gives regularity
of that identical list on the actual support-product coefficient module. -/
theorem incidenceSupportStalkModule_isWeaklyRegular_of_graphImage
    [IsIso B.projection] (w : A.incidence B)
    (rs : List ((pullback g g).presheaf.stalk
      (pullback.diagonal g
        (correspondenceTripleMiddle f g h (A.incidenceInclusion B w)))))
    (hrs : IsWeaklyRegular
      ((pullback (A.targetProjection ≫ g) g).presheaf.stalk
        (correspondenceGraph A.targetProjection g (A.incidenceFst B w)))
      (rs.map (StalkTransport.pointedMap (graphMiddlePair A.targetProjection g)
        (correspondenceGraph A.targetProjection g (A.incidenceFst B w))
        (pullback.diagonal g
          (correspondenceTripleMiddle f g h (A.incidenceInclusion B w)))
        (A.incidenceGraphMiddlePoint_eq B w)).hom)) :
    IsWeaklyRegular (A.incidenceSupportStalkModule B w)
      (rs.map (Diagonal.baseChangeStalkMap (correspondenceTriple_isPullback f g h)
        (A.incidenceInclusion B w)).hom) := by
  apply (Intersection.coefficientStalkModule_isWeaklyRegular_iff _ _ _ _ _ _).mpr
  have hlist :
      (rs.map (Diagonal.baseChangeStalkMap (correspondenceTriple_isPullback f g h)
        (A.incidenceInclusion B w)).hom).map
          (Intersection.coefficientStalkMap
            (correspondenceTripleInclusion f g h) (A.incidenceInclusion B w)
            (A.supportProductInclusion B) (A.incidenceToSupportProduct B w)
            (Intersection.point_eq _ _ _ _ (A.incidence_ambient_isPullback B) w)).hom =
      (rs.map (StalkTransport.pointedMap (graphMiddlePair A.targetProjection g)
        (correspondenceGraph A.targetProjection g (A.incidenceFst B w))
        (pullback.diagonal g
          (correspondenceTripleMiddle f g h (A.incidenceInclusion B w)))
        (A.incidenceGraphMiddlePoint_eq B w)).hom).map
          (A.incidenceGraphStalkIso B w).hom.hom := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro r _
    exact ConcreteCategory.congr_hom (A.incidenceDiagonalStalkMap_comp B w) r
  rw [hlist]
  exact StalkTransport.isWeaklyRegular_map_pointedMap
    (A.supportProductToGraphProduct B) (A.incidenceToSupportProduct B w)
    (correspondenceGraph A.targetProjection g (A.incidenceFst B w))
    (A.incidenceGraphPoint_eq B w) hrs

end Stalks

end Motivic.FiniteCorrespondenceGenerator
