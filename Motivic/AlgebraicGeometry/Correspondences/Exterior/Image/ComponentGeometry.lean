/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Incidence.IntermediateImageFiber
public import Motivic.Aglib.AlgebraicGeometry.Cycles.BaseChange.ClosedFiber
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.ImageIncidenceGenericSupport
public import Motivic.Aglib.AlgebraicGeometry.Intersection.CoefficientStalkTransport

/-!
# An image component's full exterior and its remaining incidence

An integral closed support inside the actual intermediate image is identified
with a correspondence generator by an equality of their actual image ideals.
The resulting isomorphism, its exterior base change, and the remaining
incidence square retain the original scheme morphisms and both projections.
All exterior products and remaining incidences keep their full scheme
structures. No flatness, normality or Noetherian hypothesis is needed.

The final stalk square transports the same middle equations through the
literal exterior closed-immersion quotient and the constructed scheme
isomorphism. It does not choose an unrelated scalar-ring isomorphism.
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

/-- The image scheme is identified by the two canonical inclusions of the
proved ideal equality, rather than by equality of closed carriers. -/
def imageIdealIso : (C.val.subschemeι ≫ (F.incidenceMap G).imageι).image ≅ P.scheme where
  hom := Scheme.IdealSheafData.inclusion hC.ge
  inv := Scheme.IdealSheafData.inclusion hC.le
  hom_inv_id := by simp
  inv_hom_id := by simp

/-- The support inside the whole image is the specified generator scheme. -/
def supportIso : C.val.subscheme ≅ P.scheme :=
  asIso (C.val.subschemeι ≫ (F.incidenceMap G).imageι).toImage ≪≫
    imageIdealIso F G C P hC

/-- This support identification preserves the original ambient inclusion. -/
@[reassoc (attr := simp)] theorem supportIso_ambient :
    (supportIso F G C P hC).hom ≫ P.inclusion =
      C.val.subschemeι ≫ (F.incidenceMap G).imageι := by
  simp only [supportIso, Iso.trans_hom, asIso_hom, Category.assoc,
    imageIdealIso, Scheme.IdealSheafData.inclusion_subschemeι,
    Scheme.Hom.toImage_imageι]

/-- The full image-support exterior, with no reduction after base change. -/
abbrev exterior : Scheme.{u} :=
  C.exteriorProduct ((F.incidenceMap G).imageι ≫ pullback.snd f h ≫ h)
    (H.projection ≫ h)

/-- Its literal closed immersion into the whole intermediate-image product. -/
abbrev exteriorInclusion : exterior F G H C ⟶ F.leftIntermediateImageProduct G H :=
  C.exteriorInclusion ((F.incidenceMap G).imageι ≫ pullback.snd f h ≫ h)
    (H.projection ≫ h)

/-- Exterior base change of the actual support isomorphism, over the same base. -/
def exteriorIso : exterior F G H C ≅ P.supportProduct H :=
  asIso (pullback.map _ _ _ _ (supportIso F G C P hC).hom (𝟙 H.scheme) (𝟙 S)
    (by simp only [Category.comp_id, FiniteCorrespondenceGenerator.targetProjection,
      ← Category.assoc, supportIso_ambient]) (by simp))

/-- The first exterior projection retains the canonical component identification. -/
@[reassoc (attr := simp)] theorem exteriorIso_fst :
    (exteriorIso F G H C P hC).hom ≫
      pullback.fst (P.targetProjection ≫ h) (H.projection ≫ h) =
    pullback.fst (C.val.subschemeι ≫ (F.incidenceMap G).imageι ≫
      pullback.snd f h ≫ h) (H.projection ≫ h) ≫ (supportIso F G C P hC).hom :=
  pullback.lift_fst _ _ _

/-- The exterior isomorphism keeps the third support literally unchanged. -/
@[reassoc (attr := simp)] theorem exteriorIso_snd :
    (exteriorIso F G H C P hC).hom ≫
      pullback.snd (P.targetProjection ≫ h) (H.projection ≫ h) =
    pullback.snd (C.val.subschemeι ≫ (F.incidenceMap G).imageι ≫
      pullback.snd f h ≫ h) (H.projection ≫ h) := by
  simp only [exteriorIso, asIso_hom, pullback.map, pullback.lift_snd, Category.comp_id]

/-- The inverse also retains the original support projection. -/
@[reassoc (attr := simp)] theorem exteriorIso_inv_fst :
    (exteriorIso F G H C P hC).inv ≫
      pullback.fst (C.val.subschemeι ≫ (F.incidenceMap G).imageι ≫
        pullback.snd f h ≫ h) (H.projection ≫ h) =
    pullback.fst (P.targetProjection ≫ h) (H.projection ≫ h) ≫
      (supportIso F G C P hC).inv := by
  apply (cancel_epi (exteriorIso F G H C P hC).hom).mp
  simp only [Iso.hom_inv_id_assoc, exteriorIso_fst_assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- The inverse exterior isomorphism also fixes the third support. -/
@[reassoc (attr := simp)] theorem exteriorIso_inv_snd :
    (exteriorIso F G H C P hC).inv ≫
      pullback.snd (C.val.subschemeι ≫ (F.incidenceMap G).imageι ≫
        pullback.snd f h ≫ h) (H.projection ≫ h) =
    pullback.snd (P.targetProjection ≫ h) (H.projection ≫ h) := by
  apply (cancel_epi (exteriorIso F G H C P hC).hom).mp
  simp only [Iso.hom_inv_id_assoc, exteriorIso_snd]

/-- Both constructions give the same original middle pair, as scheme maps. -/
@[reassoc] theorem exteriorInclusion_middlePair :
    exteriorInclusion F G H C ≫ F.leftImageMiddlePair G H =
      (exteriorIso F G H C P hC).hom ≫ P.supportProductInclusion H ≫
        correspondenceMiddlePair f h i := by
  apply pullback.hom_ext
  · simp only [Category.assoc, FiniteCorrespondenceGenerator.leftImageMiddlePair,
      pullback.map, pullback.lift_fst, correspondenceMiddlePair_fst,
      FiniteCorrespondenceGenerator.supportProductInclusion_fst_assoc,
      exteriorIso_fst_assoc, exteriorInclusion,
      IntegralClosedSubscheme.exteriorInclusion_fst_assoc, supportIso_ambient_assoc]
  · simp only [Category.assoc, FiniteCorrespondenceGenerator.leftImageMiddlePair,
      pullback.map, pullback.lift_snd, correspondenceMiddlePair_snd,
      FiniteCorrespondenceGenerator.supportProductInclusion_snd_assoc,
      exteriorIso_snd_assoc, exteriorInclusion,
      IntegralClosedSubscheme.exteriorInclusion_snd_assoc]
    rfl

/-- The generator's actual closed immersion into the whole intermediate image. -/
def supportInImage : P.scheme ⟶ (F.incidenceMap G).image :=
  (supportIso F G C P hC).inv ≫ C.val.subschemeι

/-- The inverse identification has the generator's literal ambient map. -/
@[reassoc (attr := simp)] theorem supportInImage_ambient :
    supportInImage F G C P hC ≫ (F.incidenceMap G).imageι = P.inclusion := by
  rw [supportInImage, Category.assoc, ← supportIso_ambient F G C P hC, Iso.inv_hom_id_assoc]

/-- In particular, the inverse support map preserves the original Z projection. -/
@[reassoc] theorem supportInImage_target :
    supportInImage F G C P hC ≫ (F.incidenceMap G).imageι ≫ pullback.snd f h =
      P.targetProjection := by
  rw [← Category.assoc, supportInImage_ambient]

/-- The actual incidence map induced by the support immersion and identity on H. -/
def remainingToImage : P.incidence H ⟶ F.leftImageIncidence G H :=
  pullback.map _ _ _ _ (supportInImage F G C P hC) (𝟙 H.scheme) (𝟙 Z)
    (by simpa only [Category.comp_id] using (supportInImage_target F G C P hC).symm)
    (by simp)

/-- The remaining-incidence map remembers the actual whole-image projection. -/
@[reassoc (attr := simp)] theorem remainingToImage_fst :
    remainingToImage F G H C P hC ≫
      pullback.fst ((F.incidenceMap G).imageι ≫ pullback.snd f h) H.projection =
    P.incidenceFst H ≫ supportInImage F G C P hC :=
  pullback.lift_fst _ _ _

/-- The remaining-incidence map retains the third support. -/
@[reassoc (attr := simp)] theorem remainingToImage_snd :
    remainingToImage F G H C P hC ≫
      pullback.snd ((F.incidenceMap G).imageι ≫ pullback.snd f h) H.projection =
    P.incidenceSnd H := by
  simp only [remainingToImage, pullback.map, pullback.lift_snd, Category.comp_id,
    FiniteCorrespondenceGenerator.incidenceSnd]

/-- The component incidence retains the original source projection through the whole image. -/
@[reassoc] theorem remainingToImage_source :
    remainingToImage F G H C P hC ≫ F.leftImageIncidenceSource G H =
      P.incidenceSource H := by
  change remainingToImage F G H C P hC ≫
      pullback.fst ((F.incidenceMap G).imageι ≫ pullback.snd f h) H.projection ≫
        (F.incidenceMap G).imageι ≫ pullback.fst f h =
      P.incidenceFst H ≫ P.inclusion ≫ pullback.fst f h
  rw [remainingToImage_fst_assoc, supportInImage_ambient_assoc]

/-- The component incidence maps to its full exterior through the constructed inverse. -/
def remainingToExterior : P.incidence H ⟶ exterior F G H C :=
  P.incidenceToSupportProduct H ≫ (exteriorIso F G H C P hC).inv

/-- The same remaining middle point is used on the whole image and on the component. -/
@[reassoc] theorem remainingToImage_middle :
    remainingToImage F G H C P hC ≫ F.leftImageIncidenceMiddle G H =
      P.incidenceFst H ≫ P.targetProjection := by
  simp only [FiniteCorrespondenceGenerator.leftImageIncidenceMiddle,
    remainingToImage_fst_assoc, supportInImage_target]

/-- The two literal remaining inclusions commute with the exterior support immersion. -/
@[reassoc] theorem remainingToImage_square :
    remainingToImage F G H C P hC ≫ F.leftImageIncidenceInclusion G H =
      remainingToExterior F G H C P hC ≫ exteriorInclusion F G H C := by
  apply pullback.hom_ext
  · simp only [Category.assoc, FiniteCorrespondenceGenerator.leftImageIncidenceInclusion_fst,
      remainingToImage_fst, remainingToExterior, exteriorInclusion,
      IntegralClosedSubscheme.exteriorInclusion_fst, exteriorIso_inv_fst_assoc,
      FiniteCorrespondenceGenerator.incidenceToSupportProduct_fst_assoc, supportInImage]
  · simp only [Category.assoc, FiniteCorrespondenceGenerator.leftImageIncidenceInclusion_snd,
      remainingToImage_snd, remainingToExterior, exteriorInclusion,
      IntegralClosedSubscheme.exteriorInclusion_snd, exteriorIso_inv_snd,
      FiniteCorrespondenceGenerator.incidenceToSupportProduct_snd]

/-- The component incidence is the inverse image of the original remaining diagonal,
transported only through the actual exterior scheme isomorphism. -/
theorem remainingDiagonal_isPullback :
    IsPullback (P.incidenceFst H ≫ P.targetProjection)
      (remainingToExterior F G H C P hC) (pullback.diagonal h)
      (exteriorInclusion F G H C ≫ F.leftImageMiddlePair G H) := by
  have hmiddle : P.supportProductInclusion H ≫ correspondenceMiddlePair f h i =
      pullback.map (P.targetProjection ≫ h) (H.projection ≫ h) h h
        P.targetProjection H.projection (𝟙 S) (by simp) (by simp) := by
    apply pullback.hom_ext
    · simp [pullback.map, Category.assoc,
        FiniteCorrespondenceGenerator.targetProjection,
        FiniteCorrespondenceGenerator.projection, correspondenceProjection]
    · simp [pullback.map, Category.assoc,
        FiniteCorrespondenceGenerator.targetProjection,
        FiniteCorrespondenceGenerator.projection, correspondenceProjection]
  have hp : IsPullback (P.incidenceFst H ≫ P.targetProjection)
      (P.incidenceToSupportProduct H) (pullback.diagonal h)
      (P.supportProductInclusion H ≫ correspondenceMiddlePair f h i) := by
    rw [hmiddle]
    exact pullback_map_diagonal_isPullback P.targetProjection H.projection h
  exact hp.of_iso (Iso.refl _) (Iso.refl _) (exteriorIso F G H C P hC).symm (Iso.refl _)
    (by simp) (by simp [remainingToExterior]) (by simp)
    (by simp only [Iso.refl_hom, Iso.symm_hom, Category.comp_id,
      exteriorInclusion_middlePair F G H C P hC, Iso.inv_hom_id_assoc])

/-- The remaining incidence of P and H is the actual Cartesian inverse image
of the whole image's remaining incidence under the exterior support immersion. -/
theorem remainingToImage_isPullback :
    IsPullback (remainingToImage F G H C P hC) (remainingToExterior F G H C P hC)
      (F.leftImageIncidenceInclusion G H) (exteriorInclusion F G H C) := by
  apply IsPullback.of_right (t := F.leftImageIncidenceRemaining_isPullback G H)
  · simpa only [remainingToImage_middle] using remainingDiagonal_isPullback F G H C P hC
  · exact remainingToImage_square F G H C P hC

/-- This actual component-incidence map is a closed immersion by base change. -/
instance remainingToImage_isClosedImmersion :
    IsClosedImmersion (remainingToImage F G H C P hC) :=
  MorphismProperty.of_isPullback (remainingToImage_isPullback F G H C P hC).flip
    (inferInstanceAs (IsClosedImmersion (exteriorInclusion F G H C)))

/-- The requested pullback is the genuine component incidence, including nilpotents. -/
def remainingPullbackIso :
    pullback (exteriorInclusion F G H C) (F.leftImageIncidenceInclusion G H) ≅ P.incidence H :=
  (remainingToImage_isPullback F G H C P hC).flip.isoPullback.symm

/-- The isomorphism retains the literal projection to the full component exterior. -/
@[reassoc (attr := simp)] theorem remainingPullbackIso_exterior :
    (remainingPullbackIso F G H C P hC).hom ≫ remainingToExterior F G H C P hC =
      pullback.fst (exteriorInclusion F G H C) (F.leftImageIncidenceInclusion G H) :=
  (remainingToImage_isPullback F G H C P hC).flip.isoPullback_inv_fst

/-- The isomorphism retains the literal projection to the whole image incidence. -/
@[reassoc (attr := simp)] theorem remainingPullbackIso_image :
    (remainingPullbackIso F G H C P hC).hom ≫ remainingToImage F G H C P hC =
      pullback.snd (exteriorInclusion F G H C) (F.leftImageIncidenceInclusion G H) :=
  (remainingToImage_isPullback F G H C P hC).flip.isoPullback_inv_snd

/-- The middle-point equality comes from the proved equality of the original maps. -/
theorem exterior_middlePoint (e : exterior F G H C) :
    F.leftImageMiddlePair G H (exteriorInclusion F G H C e) =
      (P.supportProductInclusion H ≫ correspondenceMiddlePair f h i)
        ((exteriorIso F G H C P hC).hom e) :=
  congrArg (fun m => m e) (exteriorInclusion_middlePair F G H C P hC)

/-- The actual original middle-stalk square, including the canonical equality transport. -/
theorem exterior_middleStalkSquare (e : exterior F G H C) :
    StalkTransport.pointedMap (F.leftImageMiddlePair G H)
        (exteriorInclusion F G H C e)
        (F.leftImageMiddlePair G H (exteriorInclusion F G H C e)) rfl ≫
      StalkTransport.pointedMap (exteriorInclusion F G H C) e
        (exteriorInclusion F G H C e) rfl =
    StalkTransport.pointedMap (P.supportProductInclusion H ≫ correspondenceMiddlePair f h i)
        ((exteriorIso F G H C P hC).hom e)
        (F.leftImageMiddlePair G H (exteriorInclusion F G H C e))
        (exterior_middlePoint F G H C P hC e) ≫
      StalkTransport.pointedMap (exteriorIso F G H C P hC).hom e
        ((exteriorIso F G H C P hC).hom e) rfl := by
  rw [StalkTransport.pointedMap_comp, StalkTransport.pointedMap_comp]
  exact StalkTransport.pointedMap_congr _ _
    (exteriorInclusion_middlePair F G H C P hC) _ _ _ _

/-- The identical original middle list passes through the literal immersion-kernel
quotient and then the actual exterior stalk. Its alternative expression uses
only the stalk map of the constructed exterior isomorphism. -/
theorem exterior_middleList_quotient (e : exterior F G H C)
    (s : List ((pullback h h).presheaf.stalk
      (F.leftImageMiddlePair G H (exteriorInclusion F G H C e)))) :
    ((s.map ((F.leftImageMiddlePair G H).stalkMap
        (exteriorInclusion F G H C e)).hom).map
        (Ideal.Quotient.mk (RingHom.ker ((exteriorInclusion F G H C).stalkMap e).hom))).map
        (stalkQuotientKerEquiv (exteriorInclusion F G H C) e) =
      (s.map (StalkTransport.pointedMap
        (P.supportProductInclusion H ≫ correspondenceMiddlePair f h i)
        ((exteriorIso F G H C P hC).hom e)
        (F.leftImageMiddlePair G H (exteriorInclusion F G H C e))
        (exterior_middlePoint F G H C P hC e)).hom).map
        (((exteriorIso F G H C P hC).hom).stalkMap e).hom := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro r _
  simpa only [Function.comp_apply, stalkQuotientKerEquiv,
    RingHom.quotientKerEquivOfSurjective_apply_mk, StalkTransport.pointedMap,
    TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
    Category.id_comp, CommRingCat.hom_comp, RingHom.coe_comp] using
      ConcreteCategory.congr_hom (exterior_middleStalkSquare F G H C P hC e) r

end Motivic.ExteriorImageComponentGeometry

namespace Motivic.ExteriorImageComponentGeometry
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Hom

variable (k : Type u) [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)
  (C : IntegralClosedSubscheme (F.incidenceMap G).image)
  (P : FiniteCorrespondenceGenerator X.hom Z.hom)
  (hC : (C.val.subschemeι ≫ (F.incidenceMap G).imageι).ker = P.val)

/-- Component-incidence generics remain generic in the whole image incidence:
actual source-component dominance and the finite map to X supply reflection. -/
theorem remainingToImage_mem_genericPoints (w : P.incidence H)
    (hw : w ∈ genericPoints (P.incidence H)) :
    remainingToImage F G H C P hC w ∈ genericPoints (F.leftImageIncidence G H) := by
  have := F.isFinite_leftImageIncidenceSource k G H
  apply mem_genericPoints_of_image_generic (F.leftImageIncidenceSource G H)
  change (remainingToImage F G H C P hC ≫ F.leftImageIncidenceSource G H) w ∈ _
  rw [remainingToImage_source F G H C P hC]
  exact P.incidenceSource_mem_genericPoints k H w hw

/-- The actual pushed component-incidence cycle has no nongeneric coefficient
in the whole image incidence, for arbitrary signed source-generic weights. -/
theorem remainingToImage_finitePushforward_offGeneric
    (c : genericPoints (P.incidence H) → ℤ)
    (y : F.leftImageIncidence G H) (hy : y ∉ genericPoints (F.leftImageIncidence G H)) :
    IntegralCycle.toPoints
      (IntegralCycle.finitePushforward (remainingToImage F G H C P hC)
        (IntegralCycle.ofGenericCoefficients (P.incidence H) c)) y = 0 := by
  rw [IntegralCycle.toPoints_finitePushforward_ofGenericCoefficients_apply]
  exact IntegralCycle.genericPushforwardCoefficient_eq_zero_of_not_generic
    (remainingToImage F G H C P hC)
    (fun w => remainingToImage_mem_genericPoints k F G H C P hC w.1 w.2) c y hy

end Motivic.ExteriorImageComponentGeometry
