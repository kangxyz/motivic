/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Incidence.Tor
public import Motivic.AlgebraicGeometry.Correspondences.Graph.LeftIntersectionDiagram
public import Motivic.Aglib.AlgebraicGeometry.Intersection.CoefficientStalkTransport

/-!
# Actual transposed graph-stalk scalars for left incidence

When the first support has isomorphic target projection, its product with the
second support is the transposed graph ambient product. The actual stalk ring
isomorphism intertwines the scalar maps from one and the same diagonal stalk.
This proves weak regularity on the actual coefficient module from that same
list on the transposed graph stalk, without Tor symmetry or support flatness.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingTheory.Sequence

universe u

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Products

section Stalks

variable {S X Y Z : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S}
  (A : FiniteCorrespondenceGenerator f g) (B : FiniteCorrespondenceGenerator g h)

/-- The actual middle point of the incidence embedding is the second support source. -/
theorem incidenceTripleMiddle_eq_snd (w : A.incidence B) :
    correspondenceTripleMiddle f g h (A.incidenceInclusion B w) =
      B.projection (A.incidenceSnd B w) := by
  change (A.incidenceInclusion B ≫ correspondenceTripleMiddle f g h) w = _
  have hm : A.incidenceInclusion B ≫ correspondenceTripleMiddle f g h =
      A.incidenceSnd B ≫ B.projection := by
    simp only [correspondenceTripleMiddle, incidenceInclusion_fst_assoc]
    exact A.incidence_condition B
  rw [hm]
  rfl

/-- The actual graph point is the image of the support-product incidence point. -/
theorem incidenceLeftGraphPoint_eq (w : A.incidence B) :
    _root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph B.projection g (A.incidenceSnd B w) =
      A.supportProductToLeftGraphProduct B (A.incidenceToSupportProduct B w) :=
  (congrArg (fun q => q w) (A.incidenceToSupportProduct_leftGraph B)).symm

/-- The diagonal and graph middle points are equal, using the actual incidence point. -/
theorem incidenceLeftGraphMiddlePoint_eq (w : A.incidence B) :
    pullback.diagonal g
        (correspondenceTripleMiddle f g h (A.incidenceInclusion B w)) =
      leftGraphMiddlePair B.projection g
        (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph B.projection g (A.incidenceSnd B
          w)) := by
  rw [A.incidenceTripleMiddle_eq_snd B w]
  exact (congrArg (fun q => q (A.incidenceSnd B w))
    (_root_.AlgebraicGeometry.Scheme.Products.correspondenceGraph_leftMiddlePair B.projection
      g)).symm

/-- The actual graph-product stalk is the support-product stalk by an actual ring isomorphism. -/
noncomputable def incidenceLeftGraphStalkIso [IsIso A.targetProjection] (w : A.incidence B) :
    (pullback (B.projection ≫ g) g).presheaf.stalk
        (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph B.projection g (A.incidenceSnd B
          w)) ≅
      (A.supportProduct B).presheaf.stalk (A.incidenceToSupportProduct B w) :=
  asIso (StalkTransport.pointedMap (A.supportProductToLeftGraphProduct B)
    (A.incidenceToSupportProduct B w)
    (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph B.projection g (A.incidenceSnd B w))
    (A.incidenceLeftGraphPoint_eq B w))

set_option backward.isDefEq.respectTransparency false in
/-- The two actual paths from the same diagonal stalk to the coefficient stalk agree. -/
theorem incidenceLeftDiagonalStalkMap_comp [IsIso A.targetProjection] (w : A.incidence B) :
    Diagonal.baseChangeStalkMap (correspondenceTriple_isPullback f g h)
        (A.incidenceInclusion B w) ≫
      Intersection.coefficientStalkMap
        (correspondenceTripleInclusion f g h) (A.incidenceInclusion B w)
        (A.supportProductInclusion B) (A.incidenceToSupportProduct B w)
        (Intersection.point_eq _ _ _ _ (A.incidence_ambient_isPullback B) w) =
    StalkTransport.pointedMap (leftGraphMiddlePair B.projection g)
        (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph B.projection g (A.incidenceSnd B
          w))
        (pullback.diagonal g
          (correspondenceTripleMiddle f g h (A.incidenceInclusion B w)))
        (A.incidenceLeftGraphMiddlePoint_eq B w) ≫
      (A.incidenceLeftGraphStalkIso B w).hom := by
  change StalkTransport.pointedMap (correspondenceMiddlePair f g h) _ _
      (congrArg (fun q => q (A.incidenceInclusion B w))
        (correspondenceTriple_isPullback f g h).w) ≫
      StalkTransport.pointedMap (A.supportProductInclusion B) _ _
        (Intersection.point_eq _ _ _ _ (A.incidence_ambient_isPullback B) w) =
    StalkTransport.pointedMap (leftGraphMiddlePair B.projection g) _ _
        (A.incidenceLeftGraphMiddlePoint_eq B w) ≫
      StalkTransport.pointedMap (A.supportProductToLeftGraphProduct B) _ _
        (A.incidenceLeftGraphPoint_eq B w)
  rw [StalkTransport.pointedMap_comp, StalkTransport.pointedMap_comp]
  exact StalkTransport.pointedMap_congr _ _ (A.supportProductInclusion_leftMiddlePair B) _ _ _ _

/-- Regularity of a diagonal list in the actual graph stalk gives regularity
of that identical list on the actual support-product coefficient module. -/
theorem incidenceSupportStalkModule_isWeaklyRegular_of_leftGraphImage
    [IsIso A.targetProjection] (w : A.incidence B)
    (rs : List ((pullback g g).presheaf.stalk
      (pullback.diagonal g
        (correspondenceTripleMiddle f g h (A.incidenceInclusion B w)))))
    (hrs : IsWeaklyRegular
      ((pullback (B.projection ≫ g) g).presheaf.stalk
        (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph B.projection g (A.incidenceSnd B
          w)))
      (rs.map (StalkTransport.pointedMap (leftGraphMiddlePair B.projection g)
        (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph B.projection g (A.incidenceSnd B
          w))
        (pullback.diagonal g
          (correspondenceTripleMiddle f g h (A.incidenceInclusion B w)))
        (A.incidenceLeftGraphMiddlePoint_eq B w)).hom)) :
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
      (rs.map (StalkTransport.pointedMap (leftGraphMiddlePair B.projection g)
        (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph B.projection g (A.incidenceSnd B
          w))
        (pullback.diagonal g
          (correspondenceTripleMiddle f g h (A.incidenceInclusion B w)))
        (A.incidenceLeftGraphMiddlePoint_eq B w)).hom).map
          (A.incidenceLeftGraphStalkIso B w).hom.hom := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro r _
    exact ConcreteCategory.congr_hom (A.incidenceLeftDiagonalStalkMap_comp B w) r
  rw [hlist]
  exact StalkTransport.isWeaklyRegular_map_pointedMap
    (A.supportProductToLeftGraphProduct B) (A.incidenceToSupportProduct B w)
    (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph B.projection g (A.incidenceSnd B w))
    (A.incidenceLeftGraphPoint_eq B w) hrs

end Stalks

end Motivic.FiniteCorrespondenceGenerator
