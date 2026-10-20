/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.BaseChange.Field.Pushforward
public import Motivic.AlgebraicGeometry.Correspondences.BaseChange.Field.Cycle
public import Motivic.AlgebraicGeometry.Correspondences.BaseChange.Field.IncidenceCycle

/-!
# Original component pushforward in the actual new product

The finite image of an original incidence component is its actual point closure.
This identifies its whole field pullback with the support used by the actual
field-change map, retaining the original finite degree and every new branch.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L)
  {X Y Z : SmoothSite.overField k} (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (x : genericPoints (A.incidence B))

/-- The original image generator retains exactly the ideal of the image point closure. -/
theorem fieldBaseChangeIncidenceImage_ideal :
    (A.smoothIncidenceComponentGenerator k B x).val =
      (IntegralClosedSubscheme.pointClosure (A.incidenceMap B x.1)).val := by
  rw [A.smoothIncidenceComponentGenerator_val k B x,
    IntegralClosedSubscheme.pointClosure_finiteImage]

/-- The whole new image point closure maps to the actual new source-target product. -/
def fieldBaseChangeIncidenceImageAmbientInclusion : FieldBaseChangePushforward.target φ A B x ⟶
    ((SmoothSite.fieldBaseChange φ).obj (SmoothSite.product X Z)).left :=
  pullback.lift
    (pullback.fst (FieldBaseChangePushforward.originalTargetProjection A B x ≫ X.hom)
      (Spec.map (CommRingCat.ofHom φ)) ≫
        (IntegralClosedSubscheme.pointClosure (A.incidenceMap B x.1)).val.subschemeι)
    (pullback.snd (FieldBaseChangePushforward.originalTargetProjection A B x ≫ X.hom)
      (Spec.map (CommRingCat.ofHom φ))) (by
        simpa only [FieldBaseChangePushforward.originalTargetProjection,
          SmoothSite.product_hom, Category.assoc] using
            (pullback.condition
              (f := FieldBaseChangePushforward.originalTargetProjection A B x ≫ X.hom)
              (g := Spec.map (CommRingCat.ofHom φ))))

@[reassoc]
theorem fieldBaseChangeIncidenceImageAmbientInclusion_fst :
    A.fieldBaseChangeIncidenceImageAmbientInclusion φ B x ≫
      pullback.fst (SmoothSite.product X Z).hom (Spec.map (CommRingCat.ofHom φ)) =
        pullback.fst (FieldBaseChangePushforward.originalTargetProjection A B x ≫ X.hom)
          (Spec.map (CommRingCat.ofHom φ)) ≫
            (IntegralClosedSubscheme.pointClosure (A.incidenceMap B x.1)).val.subschemeι :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem fieldBaseChangeIncidenceImageAmbientInclusion_fst_simp :
    A.fieldBaseChangeIncidenceImageAmbientInclusion φ B x ≫
      pullback.fst (pullback.fst X.hom Z.hom ≫ X.hom) (Spec.map (CommRingCat.ofHom φ)) =
        pullback.fst (FieldBaseChangePushforward.originalTargetProjection A B x ≫ X.hom)
          (Spec.map (CommRingCat.ofHom φ)) ≫
            (IntegralClosedSubscheme.pointClosure (A.incidenceMap B x.1)).val.subschemeι :=
  fieldBaseChangeIncidenceImageAmbientInclusion_fst φ A B x

@[reassoc]
theorem fieldBaseChangeIncidenceImageAmbientInclusion_snd :
    A.fieldBaseChangeIncidenceImageAmbientInclusion φ B x ≫
      pullback.snd (SmoothSite.product X Z).hom (Spec.map (CommRingCat.ofHom φ)) =
        pullback.snd (FieldBaseChangePushforward.originalTargetProjection A B x ≫ X.hom)
          (Spec.map (CommRingCat.ofHom φ)) :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)] theorem fieldBaseChangeIncidenceImageAmbientInclusion_snd_simp :
    A.fieldBaseChangeIncidenceImageAmbientInclusion φ B x ≫
      pullback.snd (pullback.fst X.hom Z.hom ≫ X.hom) (Spec.map (CommRingCat.ofHom φ)) =
        pullback.snd (FieldBaseChangePushforward.originalTargetProjection A B x ≫ X.hom)
          (Spec.map (CommRingCat.ofHom φ)) :=
  fieldBaseChangeIncidenceImageAmbientInclusion_snd φ A B x

/-- The whole image support is pulled back by its actual closed immersion. -/
theorem fieldBaseChangeIncidenceImageAmbientInclusion_isPullback :
    IsPullback
      (pullback.fst (FieldBaseChangePushforward.originalTargetProjection A B x ≫ X.hom)
        (Spec.map (CommRingCat.ofHom φ)))
      (A.fieldBaseChangeIncidenceImageAmbientInclusion φ B x)
      (IntegralClosedSubscheme.pointClosure (A.incidenceMap B x.1)).val.subschemeι
      (pullback.fst (SmoothSite.product X Z).hom (Spec.map (CommRingCat.ofHom φ))) := by
  refine IsPullback.of_bot (t := IsPullback.of_hasPullback (SmoothSite.product X Z).hom
    (Spec.map (CommRingCat.ofHom φ))) ?_
    (A.fieldBaseChangeIncidenceImageAmbientInclusion_fst φ B x).symm
  rw [fieldBaseChangeIncidenceImageAmbientInclusion_snd]
  simpa only [SmoothSite.product_hom, FieldBaseChangePushforward.originalTargetProjection,
    Category.assoc] using
      IsPullback.of_hasPullback
        (FieldBaseChangePushforward.originalTargetProjection A B x ≫ X.hom)
        (Spec.map (CommRingCat.ofHom φ))

instance fieldBaseChangeIncidenceImageAmbientInclusion_isClosedImmersion :
    IsClosedImmersion (A.fieldBaseChangeIncidenceImageAmbientInclusion φ B x) :=
  MorphismProperty.of_isPullback
    (A.fieldBaseChangeIncidenceImageAmbientInclusion_isPullback φ B x) inferInstance

/-- The whole new image support is placed in the literal new product. -/
def fieldBaseChangeIncidenceImageInclusion : FieldBaseChangePushforward.target φ A B x ⟶
    (SmoothSite.product ((SmoothSite.fieldBaseChange φ).obj X)
      ((SmoothSite.fieldBaseChange φ).obj Z)).left :=
  A.fieldBaseChangeIncidenceImageAmbientInclusion φ B x ≫
    (SmoothSite.baseChangeProductIso (Spec.map (CommRingCat.ofHom φ)) X Z).hom.left

instance fieldBaseChangeIncidenceImageInclusion_isClosedImmersion :
    IsClosedImmersion (A.fieldBaseChangeIncidenceImageInclusion φ B x) := by
  unfold fieldBaseChangeIncidenceImageInclusion
  infer_instance

/-- The original image generator's field-change cycle has exactly this whole image support. -/
theorem toIntegralCycle_fieldBaseChangeIncidenceImage :
    FiniteCorrespondence.toIntegralCycle
      ((A.smoothIncidenceComponentGenerator k B x).fieldBaseChangeCycle φ) =
      IntegralCycle.finitePushforward (A.fieldBaseChangeIncidenceImageInclusion φ B x)
        (fundamentalCycle (FieldBaseChangePushforward.target φ A B x)) := by
  let C : FiniteCorrespondenceGenerator X.hom Z.hom :=
    ⟨(IntegralClosedSubscheme.pointClosure (A.incidenceMap B x.1)).val,
      (A.fieldBaseChangeIncidenceImage_ideal B x) ▸
        (A.smoothIncidenceComponentGenerator k B x).property⟩
  have hC : A.smoothIncidenceComponentGenerator k B x = C :=
    Subtype.ext (A.fieldBaseChangeIncidenceImage_ideal B x)
  calc
    _ = FiniteCorrespondence.toIntegralCycle (C.fieldBaseChangeCycle φ) :=
      congrArg (fun D : FiniteCorrespondenceGenerator X.hom Z.hom =>
        FiniteCorrespondence.toIntegralCycle (D.fieldBaseChangeCycle φ)) hC
    _ = _ := C.toIntegralCycle_fieldBaseChangeCycle φ


open _root_.AlgebraicGeometry.Scheme.Cycles.BaseChange.ComponentDecomposition

/-- Only reassociation identifies the original component exterior with its named field pullback. -/
def fieldBaseChangeIncidenceComponentSourceIso :
    componentExterior (A.incidenceSource B ≫ X.hom)
      (Spec.map (CommRingCat.ofHom φ)) x ≅ FieldBaseChangePushforward.source φ A B x :=
  pullback.congrHom (by
    simp only [FieldBaseChangePushforward.originalSourceProjection, Category.assoc]) rfl

@[reassoc (attr := simp)]
theorem fieldBaseChangeIncidenceComponentSourceIso_hom_fst :
    (A.fieldBaseChangeIncidenceComponentSourceIso φ B x).hom ≫
      pullback.fst (FieldBaseChangePushforward.originalSourceProjection A B x ≫ X.hom)
        (Spec.map (CommRingCat.ofHom φ)) =
      pullback.fst ((IntegralClosedSubscheme.pointClosure x.1).val.subschemeι ≫
        (A.incidenceSource B ≫ X.hom)) (Spec.map (CommRingCat.ofHom φ)) := by
  simp [fieldBaseChangeIncidenceComponentSourceIso, pullback.congrHom_hom, pullback.map]

@[reassoc (attr := simp)]
theorem fieldBaseChangeIncidenceComponentSourceIso_hom_snd :
    (A.fieldBaseChangeIncidenceComponentSourceIso φ B x).hom ≫
      pullback.snd (FieldBaseChangePushforward.originalSourceProjection A B x ≫ X.hom)
        (Spec.map (CommRingCat.ofHom φ)) =
      pullback.snd ((IntegralClosedSubscheme.pointClosure x.1).val.subschemeι ≫
        (A.incidenceSource B ≫ X.hom)) (Spec.map (CommRingCat.ofHom φ)) := by
  simp [fieldBaseChangeIncidenceComponentSourceIso, pullback.congrHom_hom, pullback.map]

/-- The actual finite point-closure map with the original exterior presentation of its source. -/
def fieldBaseChangeIncidenceComponentImageMap :
    componentExterior (A.incidenceSource B ≫ X.hom)
      (Spec.map (CommRingCat.ofHom φ)) x ⟶ FieldBaseChangePushforward.target φ A B x :=
  (A.fieldBaseChangeIncidenceComponentSourceIso φ B x).hom ≫
    FieldBaseChangePushforward.map φ A B x

instance fieldBaseChangeIncidenceComponentImageMap_isFinite :
    IsFinite (A.fieldBaseChangeIncidenceComponentImageMap φ B x) := by
  unfold fieldBaseChangeIncidenceComponentImageMap
  infer_instance

/-- The whole component exterior retains the original degree after the actual finite map. -/
theorem fieldBaseChangeIncidenceComponentImageMap_pushforward :
    IntegralCycle.finitePushforward (A.fieldBaseChangeIncidenceComponentImageMap φ B x)
      (fundamentalCycle (componentExterior (A.incidenceSource B ≫ X.hom)
        (Spec.map (CommRingCat.ofHom φ)) x)) =
      ((A.incidenceMap B).residueDegree x.1 : ℤ) •
        fundamentalCycle (FieldBaseChangePushforward.target φ A B x) := by
  change IntegralCycle.finitePushforward
    ((A.fieldBaseChangeIncidenceComponentSourceIso φ B x).hom ≫
      FieldBaseChangePushforward.map φ A B x) _ = _
  rw [IntegralCycle.finitePushforward_comp,
    AddMonoidHom.comp_apply, finitePushforward_fundamentalCycle]
  exact FieldBaseChangePushforward.finitePushforward_fundamentalCycle φ A B x

/-- In the new product the whole image is the actual field-changed original generator cycle. -/
theorem fieldBaseChangeIncidenceComponentImageMap_pushforward_ambient :
    IntegralCycle.finitePushforward (A.fieldBaseChangeIncidenceImageInclusion φ B x)
      (IntegralCycle.finitePushforward (A.fieldBaseChangeIncidenceComponentImageMap φ B x)
        (fundamentalCycle (componentExterior (A.incidenceSource B ≫ X.hom)
          (Spec.map (CommRingCat.ofHom φ)) x))) =
      ((A.incidenceMap B).residueDegree x.1 : ℤ) •
        FiniteCorrespondence.toIntegralCycle
          ((A.smoothIncidenceComponentGenerator k B x).fieldBaseChangeCycle φ) := by
  rw [A.fieldBaseChangeIncidenceComponentImageMap_pushforward φ B x, map_zsmul,
    A.toIntegralCycle_fieldBaseChangeIncidenceImage φ B x]

/-- The new image immersion retains the actual finite source projection. -/
@[reassoc]
theorem fieldBaseChangeIncidenceImageInclusion_fst :
    A.fieldBaseChangeIncidenceImageInclusion φ B x ≫
      pullback.fst ((SmoothSite.fieldBaseChange φ).obj X).hom
        ((SmoothSite.fieldBaseChange φ).obj Z).hom =
      FieldBaseChangePushforward.targetProjection φ A B x := by
  unfold fieldBaseChangeIncidenceImageInclusion
  have h := congrArg (fun e => e.left)
    (SmoothSite.baseChangeProductIso_hom_fst (Spec.map (CommRingCat.ofHom φ)) X Z)
  dsimp only [MorphismProperty.Comma.comp_left, SmoothSite.productFst,
    SmoothSite.homMk_left] at h
  dsimp only [SmoothSite.fieldBaseChange]
  rw [Category.assoc, h]
  apply pullback.hom_ext
  · rw [Category.assoc, SmoothSite.baseChange_map_fst,
      FieldBaseChangePushforward.targetProjection_fst, ← Category.assoc,
      fieldBaseChangeIncidenceImageAmbientInclusion_fst]
    rfl
  · simp only [Category.assoc, SmoothSite.baseChange_map_snd,
      fieldBaseChangeIncidenceImageAmbientInclusion_snd,
      FieldBaseChangePushforward.targetProjection_snd]

@[reassoc (attr := simp)] theorem fieldBaseChangeIncidenceImageInclusion_fst_simp :
    A.fieldBaseChangeIncidenceImageInclusion φ B x ≫
      pullback.fst (pullback.snd X.hom (Spec.map (CommRingCat.ofHom φ)))
        (pullback.snd Z.hom (Spec.map (CommRingCat.ofHom φ))) =
      FieldBaseChangePushforward.targetProjection φ A B x :=
  fieldBaseChangeIncidenceImageInclusion_fst φ A B x

/-- The target coordinate is the unchanged original point-closure immersion. -/
@[reassoc]
theorem fieldBaseChangeIncidenceImageInclusion_snd_original :
    A.fieldBaseChangeIncidenceImageInclusion φ B x ≫
      pullback.snd ((SmoothSite.fieldBaseChange φ).obj X).hom
        ((SmoothSite.fieldBaseChange φ).obj Z).hom ≫
      pullback.fst Z.hom (Spec.map (CommRingCat.ofHom φ)) =
        pullback.fst (FieldBaseChangePushforward.originalTargetProjection A B x ≫ X.hom)
          (Spec.map (CommRingCat.ofHom φ)) ≫
        (IntegralClosedSubscheme.pointClosure (A.incidenceMap B x.1)).val.subschemeι ≫
          pullback.snd X.hom Z.hom := by
  unfold fieldBaseChangeIncidenceImageInclusion
  have h := congrArg (fun e => e.left)
    (SmoothSite.baseChangeProductIso_hom_snd (Spec.map (CommRingCat.ofHom φ)) X Z)
  dsimp only [MorphismProperty.Comma.comp_left, SmoothSite.productSnd,
    SmoothSite.homMk_left] at h
  dsimp only [SmoothSite.fieldBaseChange]
  rw [Category.assoc,
    ← Category.assoc (SmoothSite.baseChangeProductIso (Spec.map (CommRingCat.ofHom φ)) X Z).hom.left
      (pullback.snd ((SmoothSite.baseChange (Spec.map (CommRingCat.ofHom φ))).obj X).hom
        ((SmoothSite.baseChange (Spec.map (CommRingCat.ofHom φ))).obj Z).hom)
      (pullback.fst Z.hom (Spec.map (CommRingCat.ofHom φ))), h]
  rw [SmoothSite.baseChange_map_fst]
  dsimp only [SmoothSite.homMk_left]
  rw [← Category.assoc (A.fieldBaseChangeIncidenceImageAmbientInclusion φ B x)
      (pullback.fst (SmoothSite.product X Z).hom (Spec.map (CommRingCat.ofHom φ)))
      (pullback.snd X.hom Z.hom), fieldBaseChangeIncidenceImageAmbientInclusion_fst]
  exact Category.assoc _ _ _

@[reassoc (attr := simp)] theorem fieldBaseChangeIncidenceImageInclusion_snd_original_simp :
    A.fieldBaseChangeIncidenceImageInclusion φ B x ≫
      pullback.snd (pullback.snd X.hom (Spec.map (CommRingCat.ofHom φ)))
        (pullback.snd Z.hom (Spec.map (CommRingCat.ofHom φ))) ≫
      pullback.fst Z.hom (Spec.map (CommRingCat.ofHom φ)) =
        pullback.fst (FieldBaseChangePushforward.originalTargetProjection A B x ≫ X.hom)
          (Spec.map (CommRingCat.ofHom φ)) ≫
        (IntegralClosedSubscheme.pointClosure (A.incidenceMap B x.1)).val.subschemeι ≫
          pullback.snd X.hom Z.hom :=
  fieldBaseChangeIncidenceImageInclusion_snd_original φ A B x

/-- Both component routes agree in the actual new source-target product. -/
theorem fieldBaseChangeIncidenceComponentImageMap_ambient :
    A.fieldBaseChangeIncidenceComponentImageMap φ B x ≫
      A.fieldBaseChangeIncidenceImageInclusion φ B x =
    componentExteriorInclusion (A.incidenceSource B ≫ X.hom)
      (Spec.map (CommRingCat.ofHom φ)) x ≫
      (A.fieldBaseChangeIncidencePullbackIso φ B).inv ≫ A.fieldBaseChangeIncidenceMap φ B := by
  have hfirst :
      (A.fieldBaseChangeIncidenceComponentImageMap φ B x ≫
        A.fieldBaseChangeIncidenceImageInclusion φ B x) ≫
        pullback.fst ((SmoothSite.fieldBaseChange φ).obj X).hom
          ((SmoothSite.fieldBaseChange φ).obj Z).hom =
      (componentExteriorInclusion (A.incidenceSource B ≫ X.hom)
        (Spec.map (CommRingCat.ofHom φ)) x ≫
        (A.fieldBaseChangeIncidencePullbackIso φ B).inv ≫ A.fieldBaseChangeIncidenceMap φ B) ≫
        pullback.fst ((SmoothSite.fieldBaseChange φ).obj X).hom
          ((SmoothSite.fieldBaseChange φ).obj Z).hom := by
    apply pullback.hom_ext
    · simp only [Category.assoc, fieldBaseChangeIncidenceImageInclusion_fst,
        fieldBaseChangeIncidenceComponentImageMap,
        FieldBaseChangePushforward.map_source_assoc,
        FieldBaseChangePushforward.sourceProjection_fst,
        fieldBaseChangeIncidenceComponentSourceIso_hom_fst_assoc,
        fieldBaseChangeIncidenceMap_fst_assoc, fieldBaseChangeProjection_fst]
      rw [← fieldBaseChangeIncidenceToOriginal_fst_assoc,
        fieldBaseChangeIncidencePullbackIso_inv_original_assoc]
      simp only [componentExteriorInclusion, IntegralClosedSubscheme.exteriorInclusion_fst_assoc,
        FieldBaseChangePushforward.originalSourceProjection, incidenceSource]
    · simp only [Category.assoc, fieldBaseChangeIncidenceImageInclusion_fst,
        fieldBaseChangeIncidenceComponentImageMap,
        FieldBaseChangePushforward.map_source_assoc,
        FieldBaseChangePushforward.sourceProjection_snd,
        fieldBaseChangeIncidenceComponentSourceIso_hom_snd,
        fieldBaseChangeIncidenceMap_fst_assoc, fieldBaseChangeProjection_snd]
      have hsecond := (A.fieldBaseChangeIncidence_isPullback φ B).isoPullback_inv_snd
      calc
        _ = componentExteriorInclusion (A.incidenceSource B ≫ X.hom)
            (Spec.map (CommRingCat.ofHom φ)) x ≫
            pullback.snd (A.incidenceSource B ≫ X.hom) (Spec.map (CommRingCat.ofHom φ)) :=
          ((IntegralClosedSubscheme.pointClosure x.1).exteriorInclusion_snd _ _).symm
        _ = _ := by
          simpa only [Category.assoc, fieldBaseChangeSupportHom,
            fieldBaseChangeIncidencePullbackIso] using
            congrArg (componentExteriorInclusion (A.incidenceSource B ≫ X.hom)
              (Spec.map (CommRingCat.ofHom φ)) x ≫ ·) hsecond.symm
  apply pullback.hom_ext hfirst
  apply pullback.hom_ext
  · simp only [Category.assoc, fieldBaseChangeIncidenceImageInclusion_snd_original,
      fieldBaseChangeIncidenceComponentImageMap, FieldBaseChangePushforward.map_fst_assoc,
      fieldBaseChangeIncidenceComponentSourceIso_hom_fst_assoc,
      IntegralClosedSubscheme.pointClosureMap_ambient_assoc,
      incidenceMap_snd, fieldBaseChangeIncidenceMap_snd_assoc,
      fieldBaseChangeTargetProjection_fst]
    rw [← fieldBaseChangeIncidenceToOriginal_snd_assoc,
      fieldBaseChangeIncidencePullbackIso_inv_original_assoc]
    simp only [componentExteriorInclusion, IntegralClosedSubscheme.exteriorInclusion_fst_assoc]
  · simpa only [Category.assoc, pullback.condition, SmoothSite.fieldBaseChange_obj_hom] using
      congrArg (fun m => m ≫ ((SmoothSite.fieldBaseChange φ).obj X).hom) hfirst

/-- The actual whole component contributes its original finite degree in the new product. -/
theorem fieldBaseChangeIncidenceComponent_pushforward :
    IntegralCycle.finitePushforward (A.fieldBaseChangeIncidenceMap φ B)
      (IntegralCycle.finitePushforward (A.fieldBaseChangeIncidencePullbackIso φ B).inv
        (IntegralCycle.finitePushforward
          (componentExteriorInclusion (A.incidenceSource B ≫ X.hom)
            (Spec.map (CommRingCat.ofHom φ)) x)
          (fundamentalCycle (componentExterior (A.incidenceSource B ≫ X.hom)
            (Spec.map (CommRingCat.ofHom φ)) x)))) =
      ((A.incidenceMap B).residueDegree x.1 : ℤ) •
        FiniteCorrespondence.toIntegralCycle
          ((A.smoothIncidenceComponentGenerator k B x).fieldBaseChangeCycle φ) := by
  have h := A.fieldBaseChangeIncidenceComponentImageMap_pushforward_ambient φ B x
  rw [← AddMonoidHom.comp_apply, ← IntegralCycle.finitePushforward_comp] at h
  simp only [A.fieldBaseChangeIncidenceComponentImageMap_ambient φ B x,
    IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply] at h
  exact h

omit x in
/-- The entire signed original incidence assembly commutes with actual field change.
The finite sum keeps all original degrees and every colliding new image. -/
theorem finitePushforward_fieldBaseChangeIncidenceCycle
    (c : genericPoints (A.incidence B) → ℤ) :
    IntegralCycle.finitePushforward (A.fieldBaseChangeIncidenceMap φ B)
      (IntegralCycle.ofGenericCoefficients (A.fieldBaseChangeIncidence φ B)
        (fun w => c (A.fieldBaseChangeIncidenceOriginalGeneric φ B w) *
          A.fieldBaseChangeIncidenceFiberMultiplicity φ B w)) =
    FiniteCorrespondence.toIntegralCycle
      (FiniteCorrespondence.fieldBaseChange (X := X) (Y := Z) φ
        (A.incidenceCycleAssembly k B c)) := by
  classical
  let := IntegralCycle.genericPointFintype (A.incidence B)
  rw [A.fieldBaseChangeIncidenceCycle_eq_component_sum φ B c,
    incidenceCycleAssembly_eq_sum, map_sum, map_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [map_zsmul, map_zsmul, A.fieldBaseChangeIncidenceComponent_pushforward φ B x,
    FiniteCorrespondence.fieldBaseChange_single, map_zsmul, smul_smul]

omit x in
/-- Specialization to the original actual Tor coefficients, without replacing them
by ordinary incidence lengths or requiring positivity. -/
theorem finitePushforward_fieldBaseChangeIncidenceTorCycle :
    IntegralCycle.finitePushforward (A.fieldBaseChangeIncidenceMap φ B)
      (IntegralCycle.ofGenericCoefficients (A.fieldBaseChangeIncidence φ B)
        (fun w => A.incidenceTorCoefficient (S := Spec (.of k)) B
            (A.fieldBaseChangeIncidenceOriginalGeneric φ B w) *
          A.fieldBaseChangeIncidenceFiberMultiplicity φ B w)) =
    FiniteCorrespondence.toIntegralCycle
      (FiniteCorrespondence.fieldBaseChange (X := X) (Y := Z) φ
        (A.incidenceTorCorrespondence k B)) :=
  A.finitePushforward_fieldBaseChangeIncidenceCycle φ B
    (A.incidenceTorCoefficient (S := Spec (.of k)) B)

end Motivic.FiniteCorrespondenceGenerator
