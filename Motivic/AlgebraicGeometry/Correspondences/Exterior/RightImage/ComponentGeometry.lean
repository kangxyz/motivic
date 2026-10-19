/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Exterior.Image.ComponentGeometry
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Associativity.WholeFiber.RightRemainingList
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Incidence.Tor
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.RightFirstStageWeightedExteriorPushforward

/-!
# The right image component and its actual remaining incidence

The original image-ideal equality identifies an integral support of the G,H
image with P. The shared full right exterior is identified with F's support
product with P, preserving both projections. The remaining incidence is its
actual Cartesian intersection with the original remaining Y diagonal.

The general support identities need no smoothness. The exterior declarations
inherit Field/SmoothSite parameters from the frozen shared right exterior API;
the geometric and scalar proofs add no flatness, normality, regularity or
Noetherian premises. Only generic preservation uses the established smooth-site
finite source theorem and original incidence-source genericity.

The final scalar square uses the actual exterior isomorphism, the original
ambient diagonal map, and the actual coefficient stalk map. It transports the
same arbitrary remaining list; it makes no regularity or Euler/Tor claim.
All products retain their full scheme structures and possible nilpotents.

Source-only candidate, with a pending frozen shared prerequisite. No compiler
run, diagnostic success, live promotion, or acceptance is claimed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.ExteriorImageComponentGeometry
open _root_.AlgebraicGeometry.Scheme

variable {S Y Z W : Scheme.{u}} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  (G : FiniteCorrespondenceGenerator g h) (H : FiniteCorrespondenceGenerator h i)
  (C : IntegralClosedSubscheme (G.incidenceMap H).image)
  (P : FiniteCorrespondenceGenerator g i)
  (hC : (C.val.subschemeι ≫ (G.incidenceMap H).imageι).ker = P.val)

/-- The accepted support identification preserves the original source coordinate. -/
@[reassoc] theorem supportIso_source :
    (supportIso G H C P hC).hom ≫ P.projection =
      C.val.subschemeι ≫ (G.incidenceMap H).imageι ≫ pullback.fst g i := by
  change (supportIso G H C P hC).hom ≫ P.inclusion ≫ pullback.fst g i = _
  rw [supportIso_ambient_assoc]

/-- The actual support immersion preserves the source coordinate, over any base. -/
@[reassoc] theorem supportInImage_source :
    supportInImage G H C P hC ≫ (G.incidenceMap H).imageι ≫ pullback.fst g i =
      P.projection := by
  rw [← Category.assoc, supportInImage_ambient]
  rfl

end Motivic.ExteriorImageComponentGeometry

namespace Motivic.RightExteriorImageComponentGeometry
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Hom
open _root_.AlgebraicGeometry.Scheme.Products

open ExteriorImageComponentGeometry (supportIso supportIso_ambient supportIso_source
  supportInImage supportInImage_ambient supportInImage_source)

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)
  (C : IntegralClosedSubscheme (G.incidenceMap H).image)
  (P : FiniteCorrespondenceGenerator Y.hom W.hom)
  (hC : (C.val.subschemeι ≫ (G.incidenceMap H).imageι).ker = P.val)

/-- Exterior base change of the accepted support isomorphism, fixing F.scheme. -/
def exteriorIso : F.rightImageComponentExterior G H C ≅ F.supportProduct P := by
  let a : F.scheme ⟶ Spec (.of k) := F.targetProjection ≫ Y.hom
  let b : C.val.subscheme ⟶ Spec (.of k) :=
    C.val.subschemeι ≫ (G.incidenceMap H).imageι ≫ pullback.fst Y.hom W.hom ≫ Y.hom
  let c : P.scheme ⟶ Spec (.of k) := P.projection ≫ Y.hom
  let ha : a ≫ 𝟙 (Spec (.of k)) = 𝟙 F.scheme ≫ a :=
    (Category.comp_id a).trans (Category.id_comp a).symm
  let hb : b ≫ 𝟙 (Spec (.of k)) = (supportIso G H C P hC).hom ≫ c :=
    (Category.comp_id b).trans
      (ExteriorImageComponentGeometry.supportIso_source_assoc G H C P hC Y.hom).symm
  let q := pullback.map a b a c (𝟙 F.scheme) (supportIso G H C P hC).hom
    (𝟙 (Spec (.of k))) ha hb
  letI : IsIso q := pullback.map_isIso a b a c (𝟙 F.scheme)
    (supportIso G H C P hC).hom (𝟙 (Spec (.of k))) ha hb
  exact asIso q

/-- The first exterior projection fixes the original F support literally. -/
@[reassoc (attr := simp)] theorem exteriorIso_fst :
    (exteriorIso F G H C P hC).hom ≫
      pullback.fst (F.targetProjection ≫ Y.hom) (P.projection ≫ Y.hom) =
    pullback.fst (F.targetProjection ≫ Y.hom)
      (C.val.subschemeι ≫ (G.incidenceMap H).imageι ≫
        pullback.fst Y.hom W.hom ≫ Y.hom) := by
  simp only [exteriorIso, asIso_hom, pullback.map, pullback.lift_fst, Category.comp_id]

/-- The second exterior projection is the actual G,H support identification. -/
@[reassoc (attr := simp)] theorem exteriorIso_snd :
    (exteriorIso F G H C P hC).hom ≫
      pullback.snd (F.targetProjection ≫ Y.hom) (P.projection ≫ Y.hom) =
    pullback.snd (F.targetProjection ≫ Y.hom)
      (C.val.subschemeι ≫ (G.incidenceMap H).imageι ≫
        pullback.fst Y.hom W.hom ≫ Y.hom) ≫ (supportIso G H C P hC).hom :=
  pullback.lift_snd _ _ _

/-- The inverse exterior identification also fixes F.scheme. -/
@[reassoc (attr := simp)] theorem exteriorIso_inv_fst :
    (exteriorIso F G H C P hC).inv ≫
      pullback.fst (F.targetProjection ≫ Y.hom)
        (C.val.subschemeι ≫ (G.incidenceMap H).imageι ≫
          pullback.fst Y.hom W.hom ≫ Y.hom) =
    pullback.fst (F.targetProjection ≫ Y.hom) (P.projection ≫ Y.hom) := by
  apply (cancel_epi (exteriorIso F G H C P hC).hom).mp
  simp only [Iso.hom_inv_id_assoc, exteriorIso_fst]

/-- The inverse retains the original second support projection. -/
@[reassoc (attr := simp)] theorem exteriorIso_inv_snd :
    (exteriorIso F G H C P hC).inv ≫
      pullback.snd (F.targetProjection ≫ Y.hom)
        (C.val.subschemeι ≫ (G.incidenceMap H).imageι ≫
          pullback.fst Y.hom W.hom ≫ Y.hom) =
    pullback.snd (F.targetProjection ≫ Y.hom) (P.projection ≫ Y.hom) ≫
      (supportIso G H C P hC).inv := by
  apply (cancel_epi (exteriorIso F G H C P hC).hom).mp
  simp only [Iso.hom_inv_id_assoc, exteriorIso_snd_assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- Both routes are the original remaining Y pair, as actual scheme morphisms. -/
@[reassoc] theorem exteriorInclusion_middlePair :
    F.rightImageComponentExteriorInclusion G H C ≫ F.rightImageMiddlePair G H =
      (exteriorIso F G H C P hC).hom ≫ F.supportProductInclusion P ≫
        correspondenceMiddlePair X.hom Y.hom W.hom := by
  apply pullback.hom_ext
  · simp only [Category.assoc, FiniteCorrespondenceGenerator.rightImageMiddlePair,
      pullback.map, pullback.lift_fst, correspondenceMiddlePair_fst,
      FiniteCorrespondenceGenerator.supportProductInclusion_fst_assoc,
      exteriorIso_fst_assoc,
      FiniteCorrespondenceGenerator.rightImageComponentExteriorInclusion_fst_assoc]
  · simp only [Category.assoc, FiniteCorrespondenceGenerator.rightImageMiddlePair,
      pullback.map, pullback.lift_snd, correspondenceMiddlePair_snd,
      FiniteCorrespondenceGenerator.supportProductInclusion_snd_assoc,
      exteriorIso_snd_assoc,
      FiniteCorrespondenceGenerator.rightImageComponentExteriorInclusion_snd_assoc,
      ExteriorImageComponentGeometry.supportIso_ambient_assoc]

/-- The actual remaining-incidence map is id_F times the accepted support immersion. -/
def remainingToImage : F.incidence P ⟶ F.rightImageIncidence G H :=
  pullback.map _ _ _ _ (𝟙 F.scheme) (supportInImage G H C P hC) (𝟙 Y.left)
    (by simp)
    ((Category.comp_id (P.projection : P.scheme ⟶ Y.left)).trans
      (supportInImage_source G H C P hC).symm)

/-- The first remaining projection keeps the original F support. -/
@[reassoc (attr := simp)] theorem remainingToImage_fst :
    remainingToImage F G H C P hC ≫
      pullback.fst F.targetProjection ((G.incidenceMap H).imageι ≫
        pullback.fst Y.hom W.hom) = F.incidenceFst P := by
  simp only [remainingToImage, pullback.map, pullback.lift_fst, Category.comp_id,
    FiniteCorrespondenceGenerator.incidenceFst]

/-- The second remaining projection uses the actual support immersion. -/
@[reassoc (attr := simp)] theorem remainingToImage_snd :
    remainingToImage F G H C P hC ≫
      pullback.snd F.targetProjection ((G.incidenceMap H).imageι ≫
        pullback.fst Y.hom W.hom) =
      F.incidenceSnd P ≫ supportInImage G H C P hC :=
  pullback.lift_snd _ _ _

/-- The original source projection is unchanged on the remaining incidence. -/
@[reassoc] theorem remainingToImage_source :
    remainingToImage F G H C P hC ≫ F.rightImageIncidenceSource G H =
      F.incidenceSource P := by
  simp only [FiniteCorrespondenceGenerator.rightImageIncidenceSource,
    remainingToImage_fst_assoc, FiniteCorrespondenceGenerator.incidenceSource]

/-- The original component incidence maps into its shared full exterior. -/
def remainingToExterior : F.incidence P ⟶ F.rightImageComponentExterior G H C :=
  F.incidenceToSupportProduct P ≫ (exteriorIso F G H C P hC).inv

/-- The remaining Y coordinate is the unchanged original F target coordinate. -/
@[reassoc] theorem remainingToImage_middle :
    remainingToImage F G H C P hC ≫ F.rightImageIncidenceMiddle G H =
      F.incidenceFst P ≫ F.targetProjection := by
  simp only [FiniteCorrespondenceGenerator.rightImageIncidenceMiddle,
    remainingToImage_fst_assoc]

/-- The two literal incidence inclusions commute with the shared exterior immersion. -/
@[reassoc] theorem remainingToImage_square :
    remainingToImage F G H C P hC ≫ F.rightImageIncidenceInclusion G H =
      remainingToExterior F G H C P hC ≫
        F.rightImageComponentExteriorInclusion G H C := by
  apply pullback.hom_ext
  · simp only [Category.assoc,
      FiniteCorrespondenceGenerator.rightImageIncidenceInclusion_fst,
      remainingToImage_fst, remainingToExterior,
      FiniteCorrespondenceGenerator.rightImageComponentExteriorInclusion_fst,
      exteriorIso_inv_fst, FiniteCorrespondenceGenerator.incidenceToSupportProduct_fst]
  · simp only [Category.assoc,
      FiniteCorrespondenceGenerator.rightImageIncidenceInclusion_snd,
      remainingToImage_snd, remainingToExterior,
      FiniteCorrespondenceGenerator.rightImageComponentExteriorInclusion_snd,
      exteriorIso_inv_snd_assoc,
      FiniteCorrespondenceGenerator.incidenceToSupportProduct_snd_assoc, supportInImage]

/-- The component incidence is the actual remaining Y-diagonal inverse image,
transported through the constructed exterior scheme isomorphism. -/
theorem remainingDiagonal_isPullback :
    IsPullback (F.incidenceFst P ≫ F.targetProjection)
      (remainingToExterior F G H C P hC) (pullback.diagonal Y.hom)
      (F.rightImageComponentExteriorInclusion G H C ≫ F.rightImageMiddlePair G H) := by
  have hmiddle : F.supportProductInclusion P ≫ correspondenceMiddlePair X.hom Y.hom W.hom =
      pullback.map (F.targetProjection ≫ Y.hom) (P.projection ≫ Y.hom) Y.hom Y.hom
        F.targetProjection P.projection (𝟙 (Spec (.of k))) (by simp) (by simp) := by
    apply pullback.hom_ext
    · simp [pullback.map, Category.assoc,
        FiniteCorrespondenceGenerator.targetProjection,
        FiniteCorrespondenceGenerator.projection, correspondenceProjection]
    · simp [pullback.map, Category.assoc,
        FiniteCorrespondenceGenerator.targetProjection,
        FiniteCorrespondenceGenerator.projection, correspondenceProjection]
  have hp : IsPullback (F.incidenceFst P ≫ F.targetProjection)
      (F.incidenceToSupportProduct P) (pullback.diagonal Y.hom)
      (F.supportProductInclusion P ≫ correspondenceMiddlePair X.hom Y.hom W.hom) := by
    rw [hmiddle]
    exact pullback_map_diagonal_isPullback F.targetProjection P.projection Y.hom
  exact hp.of_iso (Iso.refl _) (Iso.refl _) (exteriorIso F G H C P hC).symm (Iso.refl _)
    (by simp) (by simp [remainingToExterior]) (by simp)
    (by simp only [Iso.refl_hom, Iso.symm_hom, Category.comp_id,
      exteriorInclusion_middlePair F G H C P hC, Iso.inv_hom_id_assoc])

/-- The component incidence is the genuine Cartesian inverse image of the
whole right image incidence under the shared full exterior support immersion. -/
theorem remainingToImage_isPullback :
    IsPullback (remainingToImage F G H C P hC) (remainingToExterior F G H C P hC)
      (F.rightImageIncidenceInclusion G H) (F.rightImageComponentExteriorInclusion G H C) := by
  apply IsPullback.of_right (t := F.rightImageIncidenceRemaining_isPullback G H)
  · simpa only [remainingToImage_middle] using remainingDiagonal_isPullback F G H C P hC
  · exact remainingToImage_square F G H C P hC

/-- The actual remaining map is a closed immersion by the proved base-change square. -/
instance remainingToImage_isClosedImmersion :
    IsClosedImmersion (remainingToImage F G H C P hC) :=
  MorphismProperty.of_isPullback (remainingToImage_isPullback F G H C P hC).flip
    (inferInstanceAs (IsClosedImmersion (F.rightImageComponentExteriorInclusion G H C)))

/-- The middle-point equality is induced by equality of the original scheme maps. -/
theorem exterior_middlePoint (e : F.rightImageComponentExterior G H C) :
    F.rightImageMiddlePair G H (F.rightImageComponentExteriorInclusion G H C e) =
      (F.supportProductInclusion P ≫ correspondenceMiddlePair X.hom Y.hom W.hom)
        ((exteriorIso F G H C P hC).hom e) :=
  congrArg (fun m => m e) (exteriorInclusion_middlePair F G H C P hC)

/-- The actual middle-stalk square retains the canonical equality transport. -/
theorem exterior_middleStalkSquare (e : F.rightImageComponentExterior G H C) :
    StalkTransport.pointedMap (F.rightImageMiddlePair G H)
        (F.rightImageComponentExteriorInclusion G H C e)
        (F.rightImageMiddlePair G H (F.rightImageComponentExteriorInclusion G H C e)) rfl ≫
      StalkTransport.pointedMap (F.rightImageComponentExteriorInclusion G H C) e
        (F.rightImageComponentExteriorInclusion G H C e) rfl =
    StalkTransport.pointedMap
        (F.supportProductInclusion P ≫ correspondenceMiddlePair X.hom Y.hom W.hom)
        ((exteriorIso F G H C P hC).hom e)
        (F.rightImageMiddlePair G H (F.rightImageComponentExteriorInclusion G H C e))
        (exterior_middlePoint F G H C P hC e) ≫
      StalkTransport.pointedMap (exteriorIso F G H C P hC).hom e
        ((exteriorIso F G H C P hC).hom e) rfl := by
  rw [StalkTransport.pointedMap_comp, StalkTransport.pointedMap_comp]
  exact StalkTransport.pointedMap_congr _ _
    (exteriorInclusion_middlePair F G H C P hC) _ _ _ _

/-- Source genericity and finite-source reflection prove image genericity;
finiteness of the component map alone would not prove this assertion. -/
theorem remainingToImage_mem_genericPoints (w : F.incidence P)
    (hw : w ∈ genericPoints (F.incidence P)) :
    remainingToImage F G H C P hC w ∈ genericPoints (F.rightImageIncidence G H) := by
  have := F.isFinite_rightImageIncidenceSource k G H
  apply mem_genericPoints_of_image_generic (F.rightImageIncidenceSource G H)
  change (remainingToImage F G H C P hC ≫ F.rightImageIncidenceSource G H) w ∈ _
  rw [remainingToImage_source F G H C P hC]
  exact F.incidenceSource_mem_genericPoints k P w hw

variable (w : F.incidence P)

/-- The original remaining-incidence square identifies the image-product point. -/
theorem remainingExterior_imagePoint :
    F.rightImageIncidenceInclusion G H (remainingToImage F G H C P hC w) =
      F.rightImageComponentExteriorInclusion G H C (remainingToExterior F G H C P hC w) :=
  congrArg (fun m => m w) (remainingToImage_square F G H C P hC)

/-- The actual exterior isomorphism returns the original support-product point. -/
theorem remainingExterior_supportPoint :
    (exteriorIso F G H C P hC).hom (remainingToExterior F G H C P hC w) =
      F.incidenceToSupportProduct P w := by
  change (remainingToExterior F G H C P hC ≫ (exteriorIso F G H C P hC).hom) w = _
  simp only [remainingToExterior, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The coefficient point is identified only by the actual incidence square
and the actual exterior isomorphism. -/
theorem remainingExterior_ambientPoint :
    correspondenceTripleInclusion X.hom Y.hom W.hom (F.incidenceInclusion P w) =
      F.supportProductInclusion P
        ((exteriorIso F G H C P hC).hom (remainingToExterior F G H C P hC w)) :=
  (Intersection.point_eq _ _ _ _ (F.incidence_ambient_isPullback P) w).trans
    (congrArg (F.supportProductInclusion P)
      (remainingExterior_supportPoint F G H C P hC w).symm)

/-- The fixed original middle point equals the actual diagonal point of the
component's original ambient triple inclusion. -/
theorem remainingExterior_middlePoint :
    F.rightImageMiddlePair G H
        (F.rightImageComponentExteriorInclusion G H C (remainingToExterior F G H C P hC w)) =
      pullback.diagonal Y.hom
        (correspondenceTripleMiddle X.hom Y.hom W.hom (F.incidenceInclusion P w)) :=
  (exterior_middlePoint F G H C P hC (remainingToExterior F G H C P hC w)).trans
    ((congrArg (correspondenceMiddlePair X.hom Y.hom W.hom)
      (remainingExterior_ambientPoint F G H C P hC w)).symm.trans
        (congrArg (fun m => m (F.incidenceInclusion P w))
          (correspondenceTriple_isPullback X.hom Y.hom W.hom).w).symm)

/-- Transport to the diagonal point uses the proved equality of original points. -/
def remainingExteriorMiddleStalkIso :
    (pullback Y.hom Y.hom).presheaf.stalk
        (F.rightImageMiddlePair G H
          (F.rightImageComponentExteriorInclusion G H C (remainingToExterior F G H C P hC w))) ≅
      (pullback Y.hom Y.hom).presheaf.stalk
        (pullback.diagonal Y.hom
          (correspondenceTripleMiddle X.hom Y.hom W.hom (F.incidenceInclusion P w))) :=
  (pullback Y.hom Y.hom).presheaf.stalkCongr
    (.of_eq (remainingExterior_middlePoint F G H C P hC w))

/-- The original middle stalk acts on the original component-incidence ambient stalk. -/
def remainingExteriorAmbientStalkMap :
    (pullback Y.hom Y.hom).presheaf.stalk
        (F.rightImageMiddlePair G H
          (F.rightImageComponentExteriorInclusion G H C (remainingToExterior F G H C P hC w))) ⟶
      F.incidenceAmbientStalk P w :=
  (remainingExteriorMiddleStalkIso F G H C P hC w).hom ≫
    Diagonal.baseChangeStalkMap (correspondenceTriple_isPullback X.hom Y.hom W.hom)
      (F.incidenceInclusion P w)

/-- The actual coefficient stalk map, at the point supplied by the exterior
isomorphism, with the original ambient Cartesian point equality retained. -/
def remainingExteriorCoefficientStalkMap :
    F.incidenceAmbientStalk P w ⟶
      (F.supportProduct P).presheaf.stalk
        ((exteriorIso F G H C P hC).hom (remainingToExterior F G H C P hC w)) :=
  Intersection.coefficientStalkMap
    (correspondenceTripleInclusion X.hom Y.hom W.hom) (F.incidenceInclusion P w)
    (F.supportProductInclusion P)
    ((exteriorIso F G H C P hC).hom (remainingToExterior F G H C P hC w))
    (remainingExterior_ambientPoint F G H C P hC w)

/-- The ambient equations are the same original list, first transported to the
actual diagonal point and then mapped by the actual flat-base-change API. -/
def remainingExteriorAmbientList
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (F.rightImageMiddlePair G H
        (F.rightImageComponentExteriorInclusion G H C (remainingToExterior F G H C P hC w))))) :
    List (F.incidenceAmbientStalk P w) :=
  (s.map (remainingExteriorMiddleStalkIso F G H C P hC w).hom.hom).map
    (Diagonal.baseChangeStalkMap (correspondenceTriple_isPullback X.hom Y.hom W.hom)
      (F.incidenceInclusion P w)).hom

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
      (F.supportProductInclusion P ≫ correspondenceMiddlePair X.hom Y.hom W.hom)
      ((exteriorIso F G H C P hC).hom (remainingToExterior F G H C P hC w))
      (F.rightImageMiddlePair G H
        (F.rightImageComponentExteriorInclusion G H C (remainingToExterior F G H C P hC w)))
      (exterior_middlePoint F G H C P hC (remainingToExterior F G H C P hC w)) := by
  rw [remainingExteriorAmbientStalkMap, Category.assoc]
  change ((pullback Y.hom Y.hom).presheaf.stalkCongr
      (.of_eq (remainingExterior_middlePoint F G H C P hC w))).hom ≫
    (StalkTransport.pointedMap (correspondenceMiddlePair X.hom Y.hom W.hom) _ _
        (congrArg (fun m => m (F.incidenceInclusion P w))
          (correspondenceTriple_isPullback X.hom Y.hom W.hom).w) ≫
      StalkTransport.pointedMap (F.supportProductInclusion P) _ _
        (remainingExterior_ambientPoint F G H C P hC w)) = _
  rw [StalkTransport.pointedMap_comp]
  exact stalkCongr_pointedMap
    (Q := F.supportProduct P) (T := pullback Y.hom Y.hom)
    (q := F.supportProductInclusion P ≫ correspondenceMiddlePair X.hom Y.hom W.hom)
    (x := (exteriorIso F G H C P hC).hom (remainingToExterior F G H C P hC w))
    (y := F.rightImageMiddlePair G H
      (F.rightImageComponentExteriorInclusion G H C (remainingToExterior F G H C P hC w)))
    (z := pullback.diagonal Y.hom
      (correspondenceTripleMiddle X.hom Y.hom W.hom (F.incidenceInclusion P w)))
    (hy := remainingExterior_middlePoint F G H C P hC w)
    (hz := (congrArg (fun m => m (F.incidenceInclusion P w))
      (correspondenceTriple_isPullback X.hom Y.hom W.hom).w).trans
        (congrArg (correspondenceMiddlePair X.hom Y.hom W.hom)
          (remainingExterior_ambientPoint F G H C P hC w)))

/-- The two actual scalar routes from the original middle stalk to the full
component exterior stalk agree. -/
theorem remainingExterior_stalkSquare :
    (F.rightImageMiddlePair G H).stalkMap
        (F.rightImageComponentExteriorInclusion G H C (remainingToExterior F G H C P hC w)) ≫
      (F.rightImageComponentExteriorInclusion G H C).stalkMap (remainingToExterior F G H C P hC w) =
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
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (F.rightImageMiddlePair G H
        (F.rightImageComponentExteriorInclusion G H C (remainingToExterior F G H C P hC w))))) :
    (F.rightTargetRemainingList G H
        (F.rightImageComponentExteriorInclusion G H C (remainingToExterior F G H C P hC w)) s).map
      ((F.rightImageComponentExteriorInclusion G H C).stalkMap
        (remainingToExterior F G H C P hC w)).hom =
    ((remainingExteriorAmbientList F G H C P hC w s).map
      (remainingExteriorCoefficientStalkMap F G H C P hC w).hom).map
        ((exteriorIso F G H C P hC).hom.stalkMap
          (remainingToExterior F G H C P hC w)).hom := by
  simp only [FiniteCorrespondenceGenerator.rightTargetRemainingList,
    remainingExteriorAmbientList, List.map_map]
  apply List.map_congr_left
  intro r _
  exact ConcreteCategory.congr_hom (remainingExterior_stalkSquare F G H C P hC w) r

/-- The same identity also retains the literal exterior immersion-kernel
quotient, by cancelling its quotient map and applying the original scalar identity. -/
theorem remainingExterior_list_quotient_identity
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (F.rightImageMiddlePair G H
        (F.rightImageComponentExteriorInclusion G H C (remainingToExterior F G H C P hC w))))) :
    ((F.rightTargetRemainingList G H
        (F.rightImageComponentExteriorInclusion G H C (remainingToExterior F G H C P hC w)) s).map
      (Ideal.Quotient.mk (RingHom.ker
        ((F.rightImageComponentExteriorInclusion G H C).stalkMap
          (remainingToExterior F G H C P hC w)).hom))).map
      (stalkQuotientKerEquiv (F.rightImageComponentExteriorInclusion G H C)
        (remainingToExterior F G H C P hC w)) =
    ((remainingExteriorAmbientList F G H C P hC w s).map
      (remainingExteriorCoefficientStalkMap F G H C P hC w).hom).map
        ((exteriorIso F G H C P hC).hom.stalkMap
          (remainingToExterior F G H C P hC w)).hom := by
  calc
    _ = (F.rightTargetRemainingList G H
        (F.rightImageComponentExteriorInclusion G H C (remainingToExterior F G H C P hC w)) s).map
        ((F.rightImageComponentExteriorInclusion G H C).stalkMap
          (remainingToExterior F G H C P hC w)).hom := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro r _
      simp only [Function.comp_apply, stalkQuotientKerEquiv,
        RingHom.quotientKerEquivOfSurjective_apply_mk]
    _ = _ := remainingExterior_list_scalar_identity F G H C P hC w s

end Motivic.RightExteriorImageComponentGeometry
