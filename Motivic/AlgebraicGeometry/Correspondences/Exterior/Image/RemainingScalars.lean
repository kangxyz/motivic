/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Exterior.Image.ComponentGeometry
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Associativity.WholeFiber.RemainingList
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Incidence.Tor

/-!
# The original remaining list through a component's actual coefficient scalars

At a point of the component incidence, its literal remaining-incidence map
determines a point of the full component exterior. The actual exterior
isomorphism identifies its support-product point with the original incidence
point. The two ambient Cartesian squares then identify the original middle
point with the diagonal point used by `Diagonal.baseChangeStalkMap`.

The resulting ambient list is the original middle list, transported by that
proved point equality and mapped through the original ambient middle map.
Its image through the actual coefficient stalk map and exterior stalk
isomorphism is the image of the original target remaining list through the
literal exterior closed immersion. The final statement retains the original
immersion-kernel quotient as well.

These are scalar and list identities for every middle list. They require no
regularity, flatness, genericity, smoothness, or Noetherian hypotheses. In
particular, they do not assert regularity after a closed-immersion base change.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.ExteriorImageComponentGeometry
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Products

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)
  (C : IntegralClosedSubscheme (F.incidenceMap G).image)
  (P : FiniteCorrespondenceGenerator f h)
  (hC : (C.val.subschemeι ≫ (F.incidenceMap G).imageι).ker = P.val)
  (w : P.incidence H)

/-- The original remaining-incidence square identifies the image-product point. -/
theorem remainingExterior_imagePoint :
    F.leftImageIncidenceInclusion G H (remainingToImage F G H C P hC w) =
      exteriorInclusion F G H C (remainingToExterior F G H C P hC w) :=
  congrArg (fun m => m w) (remainingToImage_square F G H C P hC)

/-- The actual exterior isomorphism returns the original support-product point. -/
theorem remainingExterior_supportPoint :
    (exteriorIso F G H C P hC).hom (remainingToExterior F G H C P hC w) =
      P.incidenceToSupportProduct H w := by
  change (remainingToExterior F G H C P hC ≫ (exteriorIso F G H C P hC).hom) w = _
  simp only [remainingToExterior, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The coefficient point is identified only by the actual incidence square
and the actual exterior isomorphism. -/
theorem remainingExterior_ambientPoint :
    correspondenceTripleInclusion f h i (P.incidenceInclusion H w) =
      P.supportProductInclusion H
        ((exteriorIso F G H C P hC).hom (remainingToExterior F G H C P hC w)) :=
  (Intersection.point_eq _ _ _ _ (P.incidence_ambient_isPullback H) w).trans
    (congrArg (P.supportProductInclusion H)
      (remainingExterior_supportPoint F G H C P hC w).symm)

/-- The fixed original middle point equals the actual diagonal point of the
component's original ambient triple inclusion. -/
theorem remainingExterior_middlePoint :
    F.leftImageMiddlePair G H
        (exteriorInclusion F G H C (remainingToExterior F G H C P hC w)) =
      pullback.diagonal h (correspondenceTripleMiddle f h i (P.incidenceInclusion H w)) :=
  (exterior_middlePoint F G H C P hC (remainingToExterior F G H C P hC w)).trans
    ((congrArg (correspondenceMiddlePair f h i)
      (remainingExterior_ambientPoint F G H C P hC w)).symm.trans
        (congrArg (fun m => m (P.incidenceInclusion H w))
          (correspondenceTriple_isPullback f h i).w).symm)

/-- Transport to the diagonal point uses the proved equality of original points. -/
def remainingExteriorMiddleStalkIso :
    (pullback h h).presheaf.stalk
        (F.leftImageMiddlePair G H
          (exteriorInclusion F G H C (remainingToExterior F G H C P hC w))) ≅
      (pullback h h).presheaf.stalk
        (pullback.diagonal h
          (correspondenceTripleMiddle f h i (P.incidenceInclusion H w))) :=
  (pullback h h).presheaf.stalkCongr
    (.of_eq (remainingExterior_middlePoint F G H C P hC w))

/-- The original middle stalk acts on the original component-incidence ambient stalk. -/
def remainingExteriorAmbientStalkMap :
    (pullback h h).presheaf.stalk
        (F.leftImageMiddlePair G H
          (exteriorInclusion F G H C (remainingToExterior F G H C P hC w))) ⟶
      P.incidenceAmbientStalk H w :=
  (remainingExteriorMiddleStalkIso F G H C P hC w).hom ≫
    Diagonal.baseChangeStalkMap (correspondenceTriple_isPullback f h i)
      (P.incidenceInclusion H w)

/-- The actual coefficient stalk map, at the point supplied by the exterior
isomorphism, with the original ambient Cartesian point equality retained. -/
def remainingExteriorCoefficientStalkMap :
    P.incidenceAmbientStalk H w ⟶
      (P.supportProduct H).presheaf.stalk
        ((exteriorIso F G H C P hC).hom (remainingToExterior F G H C P hC w)) :=
  Intersection.coefficientStalkMap
    (correspondenceTripleInclusion f h i) (P.incidenceInclusion H w)
    (P.supportProductInclusion H)
    ((exteriorIso F G H C P hC).hom (remainingToExterior F G H C P hC w))
    (remainingExterior_ambientPoint F G H C P hC w)

/-- The ambient equations are the same original list, first transported to the
actual diagonal point and then mapped by the actual flat-base-change API. -/
def remainingExteriorAmbientList
    (s : List ((pullback h h).presheaf.stalk
      (F.leftImageMiddlePair G H
        (exteriorInclusion F G H C (remainingToExterior F G H C P hC w))))) :
    List (P.incidenceAmbientStalk H w) :=
  (s.map (remainingExteriorMiddleStalkIso F G H C P hC w).hom.hom).map
    (Diagonal.baseChangeStalkMap (correspondenceTriple_isPullback f h i)
      (P.incidenceInclusion H w)).hom

private theorem stalkCongr_pointedMap {Q T : Scheme.{u}} (q : Q ⟶ T)
    (x : Q) (y z : T) (hy : y = z) (hz : z = q x) :
    (T.presheaf.stalkCongr (.of_eq hy)).hom ≫ StalkTransport.pointedMap q x z hz =
      StalkTransport.pointedMap q x y (hy.trans hz) := by
  subst z
  simp [StalkTransport.pointedMap]

/-- The ambient and coefficient routes are the literal pointed middle map. -/
theorem remainingExteriorAmbientStalkMap_comp :
    remainingExteriorAmbientStalkMap F G H C P hC w ≫
      remainingExteriorCoefficientStalkMap F G H C P hC w =
    StalkTransport.pointedMap
      (P.supportProductInclusion H ≫ correspondenceMiddlePair f h i)
      ((exteriorIso F G H C P hC).hom (remainingToExterior F G H C P hC w))
      (F.leftImageMiddlePair G H
        (exteriorInclusion F G H C (remainingToExterior F G H C P hC w)))
      (exterior_middlePoint F G H C P hC (remainingToExterior F G H C P hC w)) := by
  rw [remainingExteriorAmbientStalkMap, Category.assoc]
  change ((pullback h h).presheaf.stalkCongr
      (.of_eq (remainingExterior_middlePoint F G H C P hC w))).hom ≫
    (StalkTransport.pointedMap (correspondenceMiddlePair f h i) _ _
        (congrArg (fun m => m (P.incidenceInclusion H w))
          (correspondenceTriple_isPullback f h i).w) ≫
      StalkTransport.pointedMap (P.supportProductInclusion H) _ _
        (remainingExterior_ambientPoint F G H C P hC w)) = _
  rw [StalkTransport.pointedMap_comp]
  exact stalkCongr_pointedMap
    (Q := P.supportProduct H) (T := pullback h h)
    (q := P.supportProductInclusion H ≫ correspondenceMiddlePair f h i)
    (x := (exteriorIso F G H C P hC).hom (remainingToExterior F G H C P hC w))
    (y := F.leftImageMiddlePair G H
      (exteriorInclusion F G H C (remainingToExterior F G H C P hC w)))
    (z := pullback.diagonal h (correspondenceTripleMiddle f h i (P.incidenceInclusion H w)))
    (hy := remainingExterior_middlePoint F G H C P hC w)
    (hz := (congrArg (fun m => m (P.incidenceInclusion H w))
      (correspondenceTriple_isPullback f h i).w).trans
        (congrArg (correspondenceMiddlePair f h i)
          (remainingExterior_ambientPoint F G H C P hC w)))

/-- The two actual scalar routes from the original middle stalk to the full
component exterior stalk agree. -/
theorem remainingExterior_stalkSquare :
    (F.leftImageMiddlePair G H).stalkMap
        (exteriorInclusion F G H C (remainingToExterior F G H C P hC w)) ≫
      (exteriorInclusion F G H C).stalkMap (remainingToExterior F G H C P hC w) =
    remainingExteriorAmbientStalkMap F G H C P hC w ≫
      remainingExteriorCoefficientStalkMap F G H C P hC w ≫
        (exteriorIso F G H C P hC).hom.stalkMap (remainingToExterior F G H C P hC w) := by
  rw [← Category.assoc, remainingExteriorAmbientStalkMap_comp]
  simpa only [StalkTransport.pointedMap, TopCat.Presheaf.stalkCongr_hom,
    TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp] using
      exterior_middleStalkSquare F G H C P hC (remainingToExterior F G H C P hC w)

/-- The original target remaining list and the original ambient list have
identical images through the actual closed-immersion and coefficient scalars. -/
theorem remainingExterior_list_scalar_identity
    (s : List ((pullback h h).presheaf.stalk
      (F.leftImageMiddlePair G H
        (exteriorInclusion F G H C (remainingToExterior F G H C P hC w))))) :
    (F.leftTargetRemainingList G H
        (exteriorInclusion F G H C (remainingToExterior F G H C P hC w)) s).map
      ((exteriorInclusion F G H C).stalkMap (remainingToExterior F G H C P hC w)).hom =
    ((remainingExteriorAmbientList F G H C P hC w s).map
      (remainingExteriorCoefficientStalkMap F G H C P hC w).hom).map
        ((exteriorIso F G H C P hC).hom.stalkMap
          (remainingToExterior F G H C P hC w)).hom := by
  simp only [FiniteCorrespondenceGenerator.leftTargetRemainingList,
    remainingExteriorAmbientList, List.map_map]
  apply List.map_congr_left
  intro r _
  exact ConcreteCategory.congr_hom (remainingExterior_stalkSquare F G H C P hC w) r

/-- The same identity also retains the literal exterior immersion-kernel
quotient, by cancelling its quotient map and applying the original scalar identity. -/
theorem remainingExterior_list_quotient_identity
    (s : List ((pullback h h).presheaf.stalk
      (F.leftImageMiddlePair G H
        (exteriorInclusion F G H C (remainingToExterior F G H C P hC w))))) :
    ((F.leftTargetRemainingList G H
        (exteriorInclusion F G H C (remainingToExterior F G H C P hC w)) s).map
      (Ideal.Quotient.mk (RingHom.ker
        ((exteriorInclusion F G H C).stalkMap (remainingToExterior F G H C P hC w)).hom))).map
      (stalkQuotientKerEquiv (exteriorInclusion F G H C)
        (remainingToExterior F G H C P hC w)) =
    ((remainingExteriorAmbientList F G H C P hC w s).map
      (remainingExteriorCoefficientStalkMap F G H C P hC w).hom).map
        ((exteriorIso F G H C P hC).hom.stalkMap
          (remainingToExterior F G H C P hC w)).hom := by
  calc
    _ = (F.leftTargetRemainingList G H
        (exteriorInclusion F G H C (remainingToExterior F G H C P hC w)) s).map
        ((exteriorInclusion F G H C).stalkMap (remainingToExterior F G H C P hC w)).hom := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro r _
      simp only [Function.comp_apply, stalkQuotientKerEquiv,
        RingHom.quotientKerEquivOfSurjective_apply_mk]
    _ = _ := remainingExterior_list_scalar_identity F G H C P hC w s

end Motivic.ExteriorImageComponentGeometry
