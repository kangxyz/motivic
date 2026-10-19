/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightOne.FundamentalNorm
public import Motivic.Cohomology.SuslinVoevodsky.RawFieldChange
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.FiniteSchemeNormBaseChange
public import Motivic.AlgebraicGeometry.Correspondences.Graph.Flat.LeftComposition
public import Motivic.AlgebraicGeometry.Correspondences.Exterior.Simplex.GraphInterchangeRight

/-!
# Actual point norms under arbitrary field change

The actual signed cycle map retains the whole scheme-theoretic support and
its original local lengths. The determinant norm commutes with this map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

namespace Motivic.WeightOneNormFieldChange
open _root_.AlgebraicGeometry.Scheme

open WeightOnePointNorm
open _root_.AlgebraicGeometry.Scheme.FiniteAlgebra
open _root_.Motivic.WeightOneFundamentalNorm

section GraphTransport

variable {k : Type u} [Field k] {X Y Z : SmoothSite (Spec (.of k))}

local instance (X : SmoothSite (Spec (.of k))) : IsNoetherian ((𝟭 Scheme).obj X.left) :=
  inferInstanceAs (IsNoetherian X.left)

local instance (X : SmoothSite (Spec (.of k))) : IsReduced ((𝟭 Scheme).obj X.left) :=
  inferInstanceAs (IsReduced X.left)

local instance (A : FiniteCorrespondenceGenerator X.hom Y.hom) : IsNoetherian A.scheme :=
  isNoetherian_of_finiteType A.projection

private theorem toIntegralCycle_cycle (A : FiniteCorrespondenceGenerator X.hom Y.hom) :
    FiniteCorrespondence.toIntegralCycle A.cycle =
      IntegralCycle.finitePushforward A.inclusion (fundamentalCycle A.scheme) := by
  let : IsNoetherian (pullback X.hom Y.hom) :=
    isNoetherian_of_finiteType (pullback.fst X.hom Y.hom)
  rw [FiniteCorrespondenceGenerator.cycle, FiniteCorrespondence.toIntegralCycle_single]
  exact (closedFundamentalCycle_of_isIntegral A.val).symm

/-- Postcomposition by an actual target isomorphism is the ambient finite pushforward. -/
theorem toIntegralCycle_comp_graphIso (e : Y ≅ Z)
    (α : Cor.mk X ⟶ Cor.mk Y) :
    FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Z.hom)
      (α ≫ (Cor.graphFunctor k).map e.hom) =
      IntegralCycle.finitePushforward
        (SmoothSite.productIso (Iso.refl X) e).hom.left
        (FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Y.hom) α) := by
  classical
  let F := (FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := Z)).flip
    (componentGraphCycleOver e.hom.left (MorphismProperty.Over.w e.hom))
  change FiniteCorrespondence.toIntegralCycle (F α) = _
  induction α using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add α β hα hβ => simp only [map_add, hα, hβ]
  | single A n =>
    have hc : A.graphPostcompositionMap e.hom.left (MorphismProperty.Over.w e.hom) =
        A.inclusion ≫ (SmoothSite.productIso (Iso.refl X) e).hom.left := by
      apply pullback.hom_ext
      · simp only [FiniteCorrespondenceGenerator.graphPostcompositionMap_fst,
          Category.assoc]
        change A.projection = A.inclusion ≫
          (SmoothSite.productMap (𝟙 X) e.hom).left ≫ pullback.fst X.hom Z.hom
        simp only [SmoothSite.productMap, SmoothSite.productLift, SmoothSite.productFst,
          SmoothSite.productSnd, SmoothSite.homMk_left, MorphismProperty.Comma.comp_left,
          pullback.lift_fst, Category.comp_id]
        rfl
      · simp only [FiniteCorrespondenceGenerator.graphPostcompositionMap_snd,
          Category.assoc]
        change A.targetProjection ≫ e.hom.left = A.inclusion ≫
          (SmoothSite.productMap (𝟙 X) e.hom).left ≫ pullback.snd X.hom Z.hom
        simp [SmoothSite.productMap, SmoothSite.productLift, SmoothSite.productFst,
          SmoothSite.productSnd]
    have h := A.toIntegralCycle_incidenceTorPairing_componentGraph_right
      k e.hom.left (MorphismProperty.Over.w e.hom)
    change FiniteCorrespondence.toIntegralCycle (F A.cycle) = _ at h
    simp only [hc, IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply,
      ← toIntegralCycle_cycle] at h
    have hn : Finsupp.single A n = n • A.cycle := by
      simp [FiniteCorrespondenceGenerator.cycle, Finsupp.smul_single]
    rw [hn, map_zsmul, map_zsmul, map_zsmul, map_zsmul, h]
    rfl

/-- Precomposition by the inverse source comparison transports the whole signed cycle. -/
theorem toIntegralCycle_graphIso_comp (e : X ≅ Y)
    [IsIntegral X.left] [IsIntegral Y.left] [Subsingleton Y.left]
    (α : Cor.mk Y ⟶ Cor.mk Z) :
    FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Z.hom)
      ((Cor.graphFunctor k).map e.hom ≫ α) =
      IntegralCycle.finitePushforward
        (SmoothSite.productIso e.symm (Iso.refl Z)).hom.left
        (FiniteCorrespondence.toIntegralCycle (f := Y.hom) (g := Z.hom) α) := by
  classical
  let : IsIntegral ((𝟭 Scheme).obj X.left) := inferInstanceAs (IsIntegral X.left)
  let : IsIntegral ((𝟭 Scheme).obj Y.left) := inferInstanceAs (IsIntegral Y.left)
  let : Subsingleton ((𝟭 Scheme).obj Y.left) := inferInstanceAs (Subsingleton Y.left)
  let F := FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := Z)
    (componentGraphCycleOver e.hom.left (MorphismProperty.Over.w e.hom))
  change FiniteCorrespondence.toIntegralCycle (F α) = _
  induction α using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add α β hα hβ => simp only [map_add, hα, hβ]
  | single A n =>
    let : Flat A.projection := inferInstance
    have hc : A.graphPullbackMap e.hom.left (MorphismProperty.Over.w e.hom) =
        pullback.snd e.hom.left A.projection ≫ A.inclusion ≫
          (SmoothSite.productIso e.symm (Iso.refl Z)).hom.left := by
      apply pullback.hom_ext
      · simp only [FiniteCorrespondenceGenerator.graphPullbackMap_fst, Category.assoc]
        change pullback.fst e.hom.left A.projection =
          pullback.snd e.hom.left A.projection ≫ A.inclusion ≫
            (SmoothSite.productMap e.inv (𝟙 Z)).left ≫ pullback.fst X.hom Z.hom
        simp only [SmoothSite.productMap, SmoothSite.productLift, SmoothSite.productFst,
          SmoothSite.productSnd, SmoothSite.homMk_left, MorphismProperty.Comma.comp_left,
          pullback.lift_fst]
        change pullback.fst e.hom.left A.projection =
          pullback.snd e.hom.left A.projection ≫ A.projection ≫ e.inv.left
        apply (cancel_mono e.hom.left).mp
        rw [Category.assoc, Category.assoc]
        have hi : e.inv.left ≫ e.hom.left = 𝟙 Y.left :=
          congrArg (fun f => f.left) e.inv_hom_id
        rw [hi]
        exact pullback.condition.trans (congrArg
          (fun f => pullback.snd e.hom.left A.projection ≫ f)
          (Category.comp_id A.projection)).symm
      · simp only [FiniteCorrespondenceGenerator.graphPullbackMap_snd, Category.assoc]
        change pullback.snd e.hom.left A.projection ≫ A.targetProjection =
          pullback.snd e.hom.left A.projection ≫ A.inclusion ≫
            (SmoothSite.productMap e.inv (𝟙 Z)).left ≫ pullback.snd X.hom Z.hom
        simp only [SmoothSite.productMap, SmoothSite.productLift, SmoothSite.productFst,
          SmoothSite.productSnd, SmoothSite.homMk_left, MorphismProperty.Comma.comp_left,
          pullback.lift_snd, Category.comp_id]
    have h := A.toIntegralCycle_graphFunctor_comp k e.hom
    change FiniteCorrespondence.toIntegralCycle (F A.cycle) = _ at h
    simp only [hc, IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply,
      finitePushforward_fundamentalCycle, ← toIntegralCycle_cycle] at h
    have hn : Finsupp.single A n = n • A.cycle := by
      simp [FiniteCorrespondenceGenerator.cycle, Finsupp.smul_single]
    rw [hn, map_zsmul, map_zsmul, map_zsmul, map_zsmul, h]
    rfl

end GraphTransport

section FieldChange

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L)

/-- The exact product of the canonical source and torus comparisons. -/
def ambientFieldChangeIso :
    SmoothSite.product ((SmoothSite.fieldBaseChange φ).obj (SmoothSite.base (Spec (.of k))))
      ((SmoothSite.fieldBaseChange φ).obj (SmoothSite.torusPower (.of k) 1)) ≅
      SmoothSite.product (SmoothSite.base (Spec (.of L))) (SmoothSite.torusPower (.of L) 1) :=
  SmoothSite.productIso (SmoothSite.baseChangeBaseIso (Spec.map (CommRingCat.ofHom φ)))
    (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom φ) 1)

/-- The whole pulled-back support in the literal new point-torus ambient scheme. -/
def fieldChangeInclusion (A : Generator k) : A.fieldBaseChangeSupport φ ⟶ ambient L :=
  A.fieldBaseChangeInclusion φ ≫ (ambientFieldChangeIso φ).hom.left

instance (A : Generator k) : IsClosedImmersion (fieldChangeInclusion φ A) := by
  unfold fieldChangeInclusion
  infer_instance

/-- The new source coordinate is exactly the second projection of the actual field pullback. -/
@[reassoc]
theorem fieldChangeInclusion_fst (A : Generator k) :
    fieldChangeInclusion φ A ≫ pullback.fst (SmoothSite.base (Spec (.of L))).hom
      (SmoothSite.torusPower (.of L) 1).hom = A.fieldBaseChangeSupportHom φ := by
  have h := congrArg (fun f => f.left) (SmoothSite.productMap_fst
    (SmoothSite.baseChangeBaseIso (Spec.map (CommRingCat.ofHom φ))).hom
    (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom φ) 1).hom)
  change (ambientFieldChangeIso φ).hom.left ≫
      pullback.fst (SmoothSite.base (Spec (.of L))).hom
        (SmoothSite.torusPower (.of L) 1).hom =
    pullback.fst ((SmoothSite.fieldBaseChange φ).obj (SmoothSite.base (Spec (.of k)))).hom
      ((SmoothSite.fieldBaseChange φ).obj (SmoothSite.torusPower (.of k) 1)).hom ≫
        (SmoothSite.baseChangeBaseIso (Spec.map (CommRingCat.ofHom φ))).hom.left at h
  rw [fieldChangeInclusion, Category.assoc, h,
    ← Category.assoc, FiniteCorrespondenceGenerator.fieldBaseChangeInclusion_fst]
  exact A.fieldBaseChangeProjection_snd φ

private theorem fieldBaseChangeInclusion_snd (A : Generator k) :
    A.fieldBaseChangeInclusion φ ≫
      pullback.snd ((SmoothSite.fieldBaseChange φ).obj (SmoothSite.base (Spec (.of k)))).hom
        ((SmoothSite.fieldBaseChange φ).obj (SmoothSite.torusPower (.of k) 1)).hom =
      A.fieldBaseChangeTargetProjection φ := by
  unfold FiniteCorrespondenceGenerator.fieldBaseChangeInclusion
  have h := congrArg (fun f => f.left) (SmoothSite.baseChangeProductIso_hom_snd
    (Spec.map (CommRingCat.ofHom φ)) (SmoothSite.base (Spec (.of k)))
      (SmoothSite.torusPower (.of k) 1))
  dsimp only [MorphismProperty.Comma.comp_left, SmoothSite.productSnd, SmoothSite.homMk_left] at h
  dsimp only [SmoothSite.fieldBaseChange]
  rw [Category.assoc, h]
  apply pullback.hom_ext
  · rw [Category.assoc, SmoothSite.baseChange_map_fst,
      FiniteCorrespondenceGenerator.fieldBaseChangeTargetProjection_fst,
      ← Category.assoc, FiniteCorrespondenceGenerator.fieldBaseChangeAmbientInclusion_fst]
    rfl
  · simp only [Category.assoc, SmoothSite.baseChange_map_snd,
      FiniteCorrespondenceGenerator.fieldBaseChangeAmbientInclusion_snd]
    exact (A.fieldBaseChangeTargetProjection_snd φ).symm

/-- The actual target projection is retained before and after the canonical torus comparison. -/
@[reassoc]
theorem fieldChangeInclusion_snd (A : Generator k) :
    fieldChangeInclusion φ A ≫ pullback.snd (SmoothSite.base (Spec (.of L))).hom
      (SmoothSite.torusPower (.of L) 1).hom = A.fieldBaseChangeTargetProjection φ ≫
        (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom φ) 1).hom.left := by
  have h := congrArg (fun f => f.left) (SmoothSite.productMap_snd
    (SmoothSite.baseChangeBaseIso (Spec.map (CommRingCat.ofHom φ))).hom
    (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom φ) 1).hom)
  change (ambientFieldChangeIso φ).hom.left ≫
      pullback.snd (SmoothSite.base (Spec (.of L))).hom
        (SmoothSite.torusPower (.of L) 1).hom =
    pullback.snd ((SmoothSite.fieldBaseChange φ).obj (SmoothSite.base (Spec (.of k)))).hom
      ((SmoothSite.fieldBaseChange φ).obj (SmoothSite.torusPower (.of k) 1)).hom ≫
        (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom φ) 1).hom.left at h
  rw [fieldChangeInclusion, Category.assoc, h, ← Category.assoc,
    fieldBaseChangeInclusion_snd]

/-- The Laurent coordinate on the whole new support pulls back the original coordinate. -/
theorem fieldChangeInclusion_coordinate (A : Generator k) :
    fieldChangeInclusion φ A ≫ ambientCoordinate L ≫
      Spec.map (CommRingCat.PolynomialLaurent.laurentMap (CommRingCat.ofHom φ)) =
      A.fieldBaseChangeSupportToOriginal φ ≫ A.targetProjection ≫
        (SmoothSite.torusCoordinate (.of k) 1 0).left := by
  have hc := congrArg (fun f => f.left) (SmoothSite.torusPowerBaseChangeIso_coordinate
    (CommRingCat.ofHom φ) 1 0)
  dsimp only [MorphismProperty.Comma.comp_left] at hc
  have hc_assoc := congrArg (fun f => f ≫
    Spec.map (CommRingCat.PolynomialLaurent.laurentMap (CommRingCat.ofHom φ))) hc
  simp only [Category.assoc] at hc_assoc
  simp only [ambientCoordinate, Category.assoc]
  rw [fieldChangeInclusion_snd_assoc]
  erw [hc_assoc]
  rw [SmoothSite.torusBaseChangeIso_hom_coefficientMap]
  have hf := congrArg (fun f => A.fieldBaseChangeTargetProjection φ ≫ f)
    (SmoothSite.baseChange_map_fst (Spec.map (CommRingCat.ofHom φ))
      (SmoothSite.torusCoordinate (.of k) 1 0))
  have hp := congrArg (fun f => f ≫ (SmoothSite.torusCoordinate (.of k) 1 0).left)
    (A.fieldBaseChangeTargetProjection_fst φ)
  exact hf.trans ((Category.assoc _ _ _).symm.trans (hp.trans (Category.assoc _ _ _)))

/-- The exact unit on the new whole support is geometric pullback of the old unit. -/
theorem fieldChangeInclusion_coordinateUnit (A : Generator k) :
    schemeCoordinateUnit (fieldChangeInclusion φ A) =
      Units.map (A.fieldBaseChangeSupportToOriginal φ).appTop.hom.toMonoidHom
        (coordinateUnit A) := by
  apply Units.ext
  have h := congrArg (fun f => f.appTop (laurentGlobalUnit (.of k)).val)
    (fieldChangeInclusion_coordinate φ A)
  have hu := congrArg Units.val (laurentGlobalUnit_coefficient (CommRingCat.ofHom φ))
  change (Spec.map (CommRingCat.PolynomialLaurent.laurentMap (CommRingCat.ofHom φ))).appTop
      (laurentGlobalUnit (.of k)).val = (laurentGlobalUnit (.of L)).val at hu
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h
  erw [hu] at h
  exact h

/-- The whole pulled-back finite scheme has the scalar-changed original determinant norm. -/
theorem schemeNorm_fieldChangeInclusion (A : Generator k) :
    schemeNorm (A.fieldBaseChangeSupportHom φ) (fieldChangeInclusion φ A) =
      Units.map φ.toMonoidHom (generatorNorm A) := by
  have hs : FiniteSchemeNormBaseChange.scalarMap
      (A.projection ≫ (SmoothSite.base (Spec (.of k))).hom) = scalarMap A := by
    change FiniteSchemeNormBaseChange.scalarMap (A.projection ≫ 𝟙 _) = scalarMap A
    rw [Category.comp_id]
    rfl
  unfold schemeNorm
  rw [fieldChangeInclusion_coordinateUnit]
  let : IsFinite (A.projection ≫ (SmoothSite.base (Spec (.of k))).hom) := by
    change IsFinite (A.projection ≫ 𝟙 _)
    rw [Category.comp_id]
    infer_instance
  have h := FiniteSchemeNormBaseChange.normUnits_fst
    (A.projection ≫ (SmoothSite.base (Spec (.of k))).hom) φ (coordinateUnit A)
  simpa only [hs, schemeScalarMap, FiniteSchemeNormBaseChange.scalarMap,
    FiniteCorrespondenceGenerator.fieldBaseChangeSupportToOriginal,
    FiniteCorrespondenceGenerator.fieldBaseChangeSupportHom, generatorNorm,
    WeightOnePointNorm.coordinateAlgebra] using h

/-- The ordinary map on the original field's units, viewed additively. -/
def unitsFieldChange : Additive kˣ →+ Additive Lˣ :=
  (Units.map φ.toMonoidHom).toAdditive

open _root_.AlgebraicSimplex _root_.Motivic.PresheafWithTransfers

private instance baseIntegral (K : Type u) [Field K] :
    IsIntegral (SmoothSite.base (Spec (.of K))).left :=
  inferInstanceAs (IsIntegral (Spec (.of K)))

private instance baseSubsingleton (K : Type u) [Field K] :
    Subsingleton (SmoothSite.base (Spec (.of K))).left :=
  inferInstanceAs (Subsingleton (Spec (.of K)))

private instance changedBaseIntegral :
    IsIntegral ((SmoothSite.baseChange (Spec.map (CommRingCat.ofHom φ))).obj
      (SmoothSite.base (Spec (.of k)))).left :=
  IsIntegral.of_isIso (SmoothSite.baseChangeBaseIso (Spec.map (CommRingCat.ofHom φ))).inv.left

private instance changedBaseSubsingleton :
    Subsingleton ((SmoothSite.baseChange (Spec.map (CommRingCat.ofHom φ))).obj
      (SmoothSite.base (Spec (.of k)))).left :=
  (SmoothSite.baseChangeBaseIso (Spec.map (CommRingCat.ofHom φ))).hom.left.homeomorph.injective
    |>.subsingleton

/-- The actual conjugated field change is the entire finite fundamental cycle,
with the same original local lengths on the pulled-back support. -/
theorem toIntegralCycle_conjugated_fieldBaseChange_cycle (A : Generator k) :
    FiniteCorrespondence.toIntegralCycle (f := (SmoothSite.base (Spec (.of L))).hom)
      (g := (SmoothSite.torusPower (.of L) 1).hom)
      ((Cor.graphFunctor L).map
        (SmoothSite.baseChangeBaseIso (Spec.map (CommRingCat.ofHom φ))).inv ≫
          (Cor.fieldBaseChange φ).map A.cycle ≫ (Cor.graphFunctor L).map
            (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom φ) 1).hom) =
      IntegralCycle.finitePushforward (fieldChangeInclusion φ A)
        (fundamentalCycle (A.fieldBaseChangeSupport φ)) := by
  let e := SmoothSite.baseChangeBaseIso (Spec.map (CommRingCat.ofHom φ))
  let t := SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom φ) 1
  change FiniteCorrespondence.toIntegralCycle (f := (SmoothSite.base (Spec (.of L))).hom)
      (g := (SmoothSite.torusPower (.of L) 1).hom)
      ((Cor.graphFunctor L).map e.inv ≫ (Cor.fieldBaseChange φ).map A.cycle ≫
        (Cor.graphFunctor L).map t.hom) = _
  rw [← Category.assoc, toIntegralCycle_comp_graphIso t]
  erw [toIntegralCycle_graphIso_comp e.symm]
  rw [Cor.fieldBaseChange_map, FiniteCorrespondence.fieldBaseChange_cycle]
  erw [A.toIntegralCycle_fieldBaseChangeCycle φ]
  have hprod : (SmoothSite.productIso e (Iso.refl
      ((SmoothSite.baseChange (Spec.map (CommRingCat.ofHom φ))).obj
        (SmoothSite.torusPower (.of k) 1)))).hom.left ≫
      (SmoothSite.productIso (Iso.refl (SmoothSite.base (Spec (.of L)))) t).hom.left =
        (ambientFieldChangeIso φ).hom.left := by
    change (SmoothSite.productMap e.hom (𝟙 _)).left ≫
      (SmoothSite.productMap (𝟙 _) t.hom).left = _
    rw [← MorphismProperty.Comma.comp_left, ← SmoothSite.productMap_comp]
    simp only [Category.comp_id, Category.id_comp]
    rfl
  simp only [Iso.symm_symm_eq]
  rw [← AddMonoidHom.comp_apply, ← IntegralCycle.finitePushforward_comp]
  simp only [hprod]
  exact (DFunLike.congr_fun (IntegralCycle.finitePushforward_comp
    (A.fieldBaseChangeInclusion φ) (ambientFieldChangeIso φ).hom.left)
      (fundamentalCycle (A.fieldBaseChangeSupport φ))).symm


/-- On a generator the actual graph-conjugated field change has exactly the
scalar image of the original determinant norm. -/
theorem cycleNorm_conjugated_fieldBaseChange_cycle (A : Generator k) :
    cycleNorm L ((Cor.graphFunctor L).map
        (SmoothSite.baseChangeBaseIso (Spec.map (CommRingCat.ofHom φ))).inv ≫
          (Cor.fieldBaseChange φ).map A.cycle ≫ (Cor.graphFunctor L).map
            (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom φ) 1).hom) =
      unitsFieldChange φ (cycleNorm k A.cycle) := by
  let : IsFinite (A.projection ≫ (SmoothSite.base (Spec (.of k))).hom) := by
    change IsFinite (A.projection ≫ 𝟙 _)
    rw [Category.comp_id]
    infer_instance
  let : IsFinite (A.fieldBaseChangeSupportHom φ) := by
    change IsFinite (pullback.snd (A.projection ≫ (SmoothSite.base (Spec (.of k))).hom)
      (Spec.map (CommRingCat.ofHom φ)))
    infer_instance
  have h := cycleNorm_eq_norm_of_fundamental (A.fieldBaseChangeSupportHom φ)
    (fieldChangeInclusion φ A) (fieldChangeInclusion_fst φ A) _
    (toIntegralCycle_conjugated_fieldBaseChange_cycle φ A)
  rw [schemeNorm_fieldChangeInclusion] at h
  rw [cycleNorm_cycle]
  exact h

/-- Every signed point correspondence retains its determinant norm under the
actual functor, conjugated by the literal source and torus comparisons. -/
theorem cycleNorm_conjugated_fieldBaseChange (α : point k ⟶ target k) :
    cycleNorm L ((Cor.graphFunctor L).map
        (SmoothSite.baseChangeBaseIso (Spec.map (CommRingCat.ofHom φ))).inv ≫
          (Cor.fieldBaseChange φ).map α ≫ (Cor.graphFunctor L).map
            (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom φ) 1).hom) =
      unitsFieldChange φ (cycleNorm k α) := by
  classical
  induction α using Finsupp.induction_linear with
  | zero =>
    rw [Functor.map_zero, zero_comp, comp_zero, map_zero, map_zero, map_zero]
  | add α β hα hβ =>
    rw [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add,
      map_add, map_add, map_add, hα, hβ]
  | single A n =>
    have hn : Finsupp.single A n = n • A.cycle := by
      simp [FiniteCorrespondenceGenerator.cycle, Finsupp.smul_single]
    rw [hn, Functor.map_zsmul, Preadditive.zsmul_comp, Preadditive.comp_zsmul,
      map_zsmul, map_zsmul, map_zsmul, cycleNorm_conjugated_fieldBaseChange_cycle]

/-- The stable base-section adapter retains the full fundamental support. -/
theorem toIntegralCycle_baseTorusCycleFieldChange_cycle (A : Generator k) :
    FiniteCorrespondence.toIntegralCycle (f := (SmoothSite.base (Spec (.of L))).hom)
      (g := (SmoothSite.torusPower (.of L) 1).hom)
      (baseTorusCycleFieldChange φ 1 A.cycle) =
      IntegralCycle.finitePushforward (fieldChangeInclusion φ A)
        (fundamentalCycle (A.fieldBaseChangeSupport φ)) :=
  toIntegralCycle_conjugated_fieldBaseChange_cycle φ A

/-- Generator compatibility for the unchanged actual base-section cycle adapter. -/
theorem cycleNorm_baseTorusCycleFieldChange_cycle (A : Generator k) :
    cycleNorm L (baseTorusCycleFieldChange φ 1 A.cycle) =
      unitsFieldChange φ (cycleNorm k A.cycle) :=
  cycleNorm_conjugated_fieldBaseChange_cycle φ A

/-- The actual all-signed-cycle base-section adapter commutes with determinant norm. -/
theorem cycleNorm_baseTorusCycleFieldChange (α : point k ⟶ target k) :
    cycleNorm L (baseTorusCycleFieldChange φ 1 α) =
      unitsFieldChange φ (cycleNorm k α) :=
  cycleNorm_conjugated_fieldBaseChange φ α

/-- Naturality of the actual reduced-torus point norm, descended from the
literal all-signed-cycle equality. -/
theorem reducedNorm_baseReducedTorusFieldChange
    (s : sections (reducedTorus k 1) (point k)) :
    reducedNorm L (baseReducedTorusFieldChange φ 1 s) =
      unitsFieldChange φ (reducedNorm k s) := by
  obtain ⟨⟨α⟩, rfl⟩ := toReducedTorus_surjective k 1 (point k) s
  rw [baseReducedTorusFieldChange_quotient, reducedNorm_quotient,
    reducedNorm_quotient, cycleNorm_baseTorusCycleFieldChange]

end FieldChange

end Motivic.WeightOneNormFieldChange
