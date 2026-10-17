/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.IntegralExteriorCyclePushforward
public import Motivic.AlgebraicGeometry.Cycles.RightWholeFiberTorExteriorDecomposition
public import Motivic.AlgebraicGeometry.Cycles.RightExteriorImageGeneric

/-!
# The actual right degree-weighted exterior pushforward

For every ORIGINAL G,H incidence generic, take the literal exterior base change
of its point-closure map, with F.scheme as the first factor. The Cartesian square
uses the second projections. Generic preservation follows from the original
component decomposition through the actual pullback symmetry, the proved whole
right image-map genericity, and reflection through the image-support inclusion.

The existing global point-closure degree-length theorem then pushes the whole
fundamental cycle, retaining every branch and nonreduced multiplicity. Summing
retains every original label, its signed G,H Tor coefficient and its ORIGINAL
incidence residue degree, even when distinct labels have the same image support.
Only flatness of F.scheme over the field is used. There is no remaining-diagonal,
right-bracket, or associativity claim.

Source-only candidate: no compilation, diagnostic success, or acceptance claimed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

universe u

namespace Motivic.FiniteCorrespondenceGenerator

open IntegralClosedSubscheme WholeFiberTorExteriorDecomposition

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

local instance rightWeighted_toImageFinite : IsFinite (G.incidenceMap H).toImage :=
  G.incidenceToImage_isFinite H

local instance rightWeighted_factorFlat : Flat (F.targetProjection ≫ Y.hom) := by
  let : Subsingleton (Spec (.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  let : IsIntegral (Spec (.of k)) := inferInstance
  exact Flat.instOfSubsingletonCarrierCarrierCommRingCatOfIsIntegral
    (Y := Spec (.of k)) (F.targetProjection ≫ Y.hom)

local instance rightWeighted_sourceNoetherian :
    IsNoetherian (F.rightIntermediateSupportProduct G H) :=
  isNoetherian_of_finiteType
    (pullback.snd (F.targetProjection ≫ Y.hom) (G.incidenceSource H ≫ Y.hom))

local instance rightWeighted_imageBaseNoetherian :
    IsNoetherian (pullback (F.targetProjection ≫ Y.hom) Y.hom) := by
  let : IsNoetherian ((𝟭 Scheme).obj X.left) := inferInstanceAs (IsNoetherian X.left)
  let : IsNoetherian F.scheme := isNoetherian_of_finiteType F.projection
  exact isNoetherian_of_finiteType (pullback.fst (F.targetProjection ≫ Y.hom) Y.hom)

local instance rightWeighted_imageProjectionFinite :
    IsFinite (F.rightExteriorImageSourceMap G H) :=
  F.isFinite_rightExteriorImageSourceMap k G H

local instance rightWeighted_imageNoetherian :
    IsNoetherian (F.rightIntermediateImageProduct G H) :=
  isNoetherian_of_finiteType (F.rightExteriorImageSourceMap G H)

/-- The full literal F.scheme times an integral support in the original G,H image.
The exterior itself is neither reduced nor restricted to one generic branch. -/
abbrev rightImageComponentExterior
    (C : IntegralClosedSubscheme (G.incidenceMap H).image) : Scheme.{u} :=
  pullback (F.targetProjection ≫ Y.hom)
    (C.val.subschemeι ≫ (G.incidenceMap H).imageι ≫ pullback.fst Y.hom W.hom ≫ Y.hom)

/-- Its actual closed inclusion fixes F.scheme and uses the original support inclusion. -/
def rightImageComponentExteriorInclusion
    (C : IntegralClosedSubscheme (G.incidenceMap H).image) :
    F.rightImageComponentExterior G H C ⟶ F.rightIntermediateImageProduct G H :=
  pullback.map _ _ _ _ (𝟙 F.scheme) C.val.subschemeι (𝟙 (Spec (.of k)))
    (by simp) (by simp)

/-- The first support is literally unchanged by the component inclusion. -/
@[reassoc (attr := simp)] theorem rightImageComponentExteriorInclusion_fst
    (C : IntegralClosedSubscheme (G.incidenceMap H).image) :
    F.rightImageComponentExteriorInclusion G H C ≫
        pullback.fst (F.targetProjection ≫ Y.hom)
          ((G.incidenceMap H).imageι ≫ pullback.fst Y.hom W.hom ≫ Y.hom) =
      pullback.fst (F.targetProjection ≫ Y.hom)
        (C.val.subschemeι ≫ (G.incidenceMap H).imageι ≫
          pullback.fst Y.hom W.hom ≫ Y.hom) := by
  simp only [rightImageComponentExteriorInclusion, pullback.map,
    pullback.lift_fst, Category.comp_id]

/-- The second projection is the actual support inclusion. -/
@[reassoc (attr := simp)] theorem rightImageComponentExteriorInclusion_snd
    (C : IntegralClosedSubscheme (G.incidenceMap H).image) :
    F.rightImageComponentExteriorInclusion G H C ≫
        pullback.snd (F.targetProjection ≫ Y.hom)
          ((G.incidenceMap H).imageι ≫ pullback.fst Y.hom W.hom ≫ Y.hom) =
      pullback.snd (F.targetProjection ≫ Y.hom)
        (C.val.subschemeι ≫ (G.incidenceMap H).imageι ≫
          pullback.fst Y.hom W.hom ≫ Y.hom) ≫ C.val.subschemeι :=
  pullback.lift_snd _ _ _

/-- The image-component inclusion is Cartesian over its original support inclusion. -/
theorem rightImageComponentExteriorInclusion_isPullback
    (C : IntegralClosedSubscheme (G.incidenceMap H).image) :
    IsPullback
      (pullback.snd (F.targetProjection ≫ Y.hom)
        (C.val.subschemeι ≫ (G.incidenceMap H).imageι ≫
          pullback.fst Y.hom W.hom ≫ Y.hom))
      (F.rightImageComponentExteriorInclusion G H C) C.val.subschemeι
      (pullback.snd (F.targetProjection ≫ Y.hom)
        ((G.incidenceMap H).imageι ≫ pullback.fst Y.hom W.hom ≫ Y.hom)) := by
  refine IsPullback.of_bot
    (t := (IsPullback.of_hasPullback (F.targetProjection ≫ Y.hom)
      ((G.incidenceMap H).imageι ≫ pullback.fst Y.hom W.hom ≫ Y.hom)).flip) ?_
    (F.rightImageComponentExteriorInclusion_snd G H C).symm
  simpa only [rightImageComponentExteriorInclusion_fst] using
    (IsPullback.of_hasPullback (F.targetProjection ≫ Y.hom)
      (C.val.subschemeι ≫ (G.incidenceMap H).imageι ≫
        pullback.fst Y.hom W.hom ≫ Y.hom)).flip

instance rightImageComponentExteriorInclusion_isClosedImmersion
    (C : IntegralClosedSubscheme (G.incidenceMap H).image) :
    IsClosedImmersion (F.rightImageComponentExteriorInclusion G H C) :=
  MorphismProperty.of_isPullback
    (F.rightImageComponentExteriorInclusion_isPullback G H C) inferInstance

instance rightImageComponentExterior_isNoetherian
    (C : IntegralClosedSubscheme (G.incidenceMap H).image) :
    IsNoetherian (F.rightImageComponentExterior G H C) :=
  isNoetherian_of_finiteType (F.rightImageComponentExteriorInclusion G H C)

variable (z : genericPoints (G.incidence H))

/-- The actual point-closure map preserves the original structure map to the field. -/
@[reassoc] theorem rightFirstStagePointClosureMap_structure :
    pointClosureMap (G.incidenceMap H).toImage z.1 ≫
        (pointClosure ((G.incidenceMap H).toImage z.1)).val.subschemeι ≫
        (G.incidenceMap H).imageι ≫ pullback.fst Y.hom W.hom ≫ Y.hom =
      (pointClosure z.1).val.subschemeι ≫ G.incidenceSource H ≫ Y.hom := by
  simp only [pointClosureMap_ambient_assoc, Scheme.Hom.toImage_imageι_assoc,
    incidenceMap_fst_assoc, incidenceSource, projection, correspondenceProjection, Category.assoc]

/-- The actual right component map is id_F times the original point-closure map. -/
def rightFirstStageComponentExteriorMap :
    F.rightFirstStageComponentExterior G H z ⟶
      F.rightImageComponentExterior G H (pointClosure ((G.incidenceMap H).toImage z.1)) :=
  pullback.map _ _ _ _ (𝟙 F.scheme) (pointClosureMap (G.incidenceMap H).toImage z.1)
    (𝟙 (Spec (.of k))) (by simp)
    ((Category.comp_id
      ((pointClosure z.1).val.subschemeι ≫ G.incidenceSource H ≫ Y.hom :
        (pointClosure z.1).val.subscheme ⟶ Spec (.of k))).trans
      (G.rightFirstStagePointClosureMap_structure H z).symm)

/-- The first support remains literally unchanged under the component map. -/
@[reassoc (attr := simp)] theorem rightFirstStageComponentExteriorMap_fst :
    F.rightFirstStageComponentExteriorMap G H z ≫
        pullback.fst (F.targetProjection ≫ Y.hom)
          ((pointClosure ((G.incidenceMap H).toImage z.1)).val.subschemeι ≫
            (G.incidenceMap H).imageι ≫ pullback.fst Y.hom W.hom ≫ Y.hom) =
      pullback.fst (F.targetProjection ≫ Y.hom)
        ((pointClosure z.1).val.subschemeι ≫ G.incidenceSource H ≫ Y.hom) := by
  simp only [rightFirstStageComponentExteriorMap, pullback.map,
    pullback.lift_fst, Category.comp_id]

/-- The second projection uses the ORIGINAL finite point-closure map. -/
@[reassoc (attr := simp)] theorem rightFirstStageComponentExteriorMap_snd :
    F.rightFirstStageComponentExteriorMap G H z ≫
        pullback.snd (F.targetProjection ≫ Y.hom)
          ((pointClosure ((G.incidenceMap H).toImage z.1)).val.subschemeι ≫
            (G.incidenceMap H).imageι ≫ pullback.fst Y.hom W.hom ≫ Y.hom) =
      pullback.snd (F.targetProjection ≫ Y.hom)
        ((pointClosure z.1).val.subschemeι ≫ G.incidenceSource H ≫ Y.hom) ≫
        pointClosureMap (G.incidenceMap H).toImage z.1 :=
  pullback.lift_snd _ _ _

/-- The degree-length engine uses this literal second-projection Cartesian square. -/
theorem rightFirstStageComponentExteriorMap_isPullback :
    IsPullback
      (pullback.snd (F.targetProjection ≫ Y.hom)
        ((pointClosure z.1).val.subschemeι ≫ G.incidenceSource H ≫ Y.hom))
      (F.rightFirstStageComponentExteriorMap G H z)
      (pointClosureMap (G.incidenceMap H).toImage z.1)
      (pullback.snd (F.targetProjection ≫ Y.hom)
        ((pointClosure ((G.incidenceMap H).toImage z.1)).val.subschemeι ≫
          (G.incidenceMap H).imageι ≫ pullback.fst Y.hom W.hom ≫ Y.hom)) := by
  refine IsPullback.of_bot
    (t := (IsPullback.of_hasPullback (F.targetProjection ≫ Y.hom)
      ((pointClosure ((G.incidenceMap H).toImage z.1)).val.subschemeι ≫
        (G.incidenceMap H).imageι ≫ pullback.fst Y.hom W.hom ≫ Y.hom)).flip) ?_
    (F.rightFirstStageComponentExteriorMap_snd G H z).symm
  simpa only [rightFirstStageComponentExteriorMap_fst,
    rightFirstStagePointClosureMap_structure] using
    (IsPullback.of_hasPullback (F.targetProjection ≫ Y.hom)
      ((pointClosure z.1).val.subschemeι ≫ G.incidenceSource H ≫ Y.hom)).flip

instance rightFirstStageComponentExteriorMap_isFinite :
    IsFinite (F.rightFirstStageComponentExteriorMap G H z) :=
  MorphismProperty.of_isPullback
    (F.rightFirstStageComponentExteriorMap_isPullback G H z) inferInstance

/-- Both routes are the actual morphism into the whole right image product. -/
@[reassoc] theorem rightFirstStageComponentExteriorMap_ambient :
    F.rightFirstStageComponentExteriorMap G H z ≫
        F.rightImageComponentExteriorInclusion G H
          (pointClosure ((G.incidenceMap H).toImage z.1)) =
      F.rightFirstStageComponentExteriorInclusion G H z ≫
        F.rightIntermediateImageMap G H := by
  apply pullback.hom_ext
  · simp only [Category.assoc, rightImageComponentExteriorInclusion_fst,
      rightFirstStageComponentExteriorMap_fst, rightIntermediateImageMap_fst,
      rightFirstStageComponentExteriorInclusion, pullback.map,
      pullback.lift_fst, Category.comp_id]
  · simp only [Category.assoc, rightImageComponentExteriorInclusion_snd,
      rightFirstStageComponentExteriorMap_snd_assoc, rightIntermediateImageMap_snd,
      rightFirstStageComponentExteriorInclusion, pullback.map,
      pullback.lift_snd_assoc, pointClosureMap_ambient]

/-- Original component generics remain whole-right generics through the literal
pullback symmetry and the proved general component-decomposition theorem. -/
theorem rightFirstStageComponentExteriorInclusion_mem_genericPoints
    (w : genericPoints (F.rightFirstStageComponentExterior G H z)) :
    F.rightFirstStageComponentExteriorInclusion G H z w.1 ∈
      genericPoints (F.rightIntermediateSupportProduct G H) := by
  have hg :=
    (mem_genericPoints_iff_of_isIso (F.rightFirstStageExteriorSymmetry G H).hom _).mpr
      (componentExterior_generic_mem (G.incidenceSource H ≫ Y.hom)
        (F.targetProjection ≫ Y.hom) z
        (mapGenericPoint (F.rightFirstStageComponentExteriorSymmetry G H z).inv w))
  change ((F.rightFirstStageComponentExteriorSymmetry G H z).inv ≫
    componentExteriorInclusion (G.incidenceSource H ≫ Y.hom)
      (F.targetProjection ≫ Y.hom) z ≫
    (F.rightFirstStageExteriorSymmetry G H).hom) w.1 ∈ _ at hg
  rwa [← rightFirstStageComponentExteriorSymmetry_inclusion, Iso.inv_hom_id_assoc] at hg

/-- Generic preservation uses whole-map geometry, then the actual finite closed
inclusion reflects genericity. No arbitrary-finite-map preservation is assumed. -/
theorem rightFirstStageComponentExteriorMap_mem_genericPoints
    (w : genericPoints (F.rightFirstStageComponentExterior G H z)) :
    F.rightFirstStageComponentExteriorMap G H z w.1 ∈
      genericPoints (F.rightImageComponentExterior G H
        (pointClosure ((G.incidenceMap H).toImage z.1))) := by
  apply mem_genericPoints_of_image_generic
    (F.rightImageComponentExteriorInclusion G H
      (pointClosure ((G.incidenceMap H).toImage z.1)))
  change (F.rightFirstStageComponentExteriorMap G H z ≫
    F.rightImageComponentExteriorInclusion G H
      (pointClosure ((G.incidenceMap H).toImage z.1))) w.1 ∈ _
  rw [rightFirstStageComponentExteriorMap_ambient, Scheme.Hom.comp_apply]
  exact F.rightIntermediateImageMap_mem_genericPoints k G H _
    (F.rightFirstStageComponentExteriorInclusion_mem_genericPoints G H z w)

/-- Every image-exterior generic projects to its integral-support generic.
Flatness here is only the actual base change of F.scheme → Spec k. -/
theorem rightImageComponentExterior_projection_generic
    (C : IntegralClosedSubscheme (G.incidenceMap H).image)
    (v : genericPoints (F.rightImageComponentExterior G H C)) :
    pullback.snd (F.targetProjection ≫ Y.hom)
        (C.val.subschemeι ≫ (G.incidenceMap H).imageι ≫
          pullback.fst Y.hom W.hom ≫ Y.hom) v.1 = genericPoint C.val.subscheme := by
  have hg := mem_genericPoints_of_generalizing
    (pullback.snd (F.targetProjection ≫ Y.hom)
      (C.val.subschemeι ≫ (G.incidenceMap H).imageι ≫
        pullback.fst Y.hom W.hom ≫ Y.hom)) (Flat.generalizingMap _) v.1 v.2
  simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using hg

/-- Factoring through the whole scheme image preserves the ORIGINAL incidence degree. -/
theorem rightFirstStageToImage_residueDegree :
    (G.incidenceMap H).toImage.residueDegree z.1 = (G.incidenceMap H).residueDegree z.1 := by
  have he := congrArg (fun m => m.residueDegree z.1) (G.incidenceMap H).toImage_imageι
  simpa only [residueDegree_comp, residueDegree_of_surjectiveOnStalks, one_mul] using he

/-- The existing point-closure theorem gives equality of WHOLE exterior cycles,
including all branches, nilpotent multiplicities, and the original residue degree. -/
theorem rightFirstStageComponentExteriorMap_finitePushforward_fundamentalCycle :
    IntegralCycle.finitePushforward (F.rightFirstStageComponentExteriorMap G H z)
        (fundamentalCycle (F.rightFirstStageComponentExterior G H z)) =
      ((G.incidenceMap H).residueDegree z.1 : ℤ) •
        fundamentalCycle (F.rightImageComponentExterior G H
          (pointClosure ((G.incidenceMap H).toImage z.1))) := by
  have h :=
    IntegralExteriorCyclePushforward.finitePushforward_fundamentalCycle_pointClosure_baseChange
      (G.incidenceMap H).toImage z.1 (F.rightFirstStageComponentExteriorMap_isPullback G H z)
      (F.rightFirstStageComponentExteriorMap_mem_genericPoints G H z)
      (F.rightImageComponentExterior_projection_generic G H
        (pointClosure ((G.incidenceMap H).toImage z.1)))
  rwa [rightFirstStageToImage_residueDegree] at h

/-- The component identity holds inside the literal whole right image product. -/
theorem rightFirstStageComponentExterior_finitePushforward_ambient :
    IntegralCycle.finitePushforward (F.rightIntermediateImageMap G H)
        (IntegralCycle.finitePushforward (F.rightFirstStageComponentExteriorInclusion G H z)
          (fundamentalCycle (F.rightFirstStageComponentExterior G H z))) =
      ((G.incidenceMap H).residueDegree z.1 : ℤ) •
        IntegralCycle.finitePushforward
          (F.rightImageComponentExteriorInclusion G H
            (pointClosure ((G.incidenceMap H).toImage z.1)))
          (fundamentalCycle (F.rightImageComponentExterior G H
            (pointClosure ((G.incidenceMap H).toImage z.1)))) := by
  have hcongr {A B : Scheme.{u}} (f g : A ⟶ B) (hf : IsFinite f) (hg : IsFinite g)
      (h : f = g) (c : IntegralCycle A) :
      @IntegralCycle.finitePushforward A B f hf c =
        @IntegralCycle.finitePushforward A B g hg c := by
    cases h
    rfl
  calc
    _ = IntegralCycle.finitePushforward
        (F.rightFirstStageComponentExteriorInclusion G H z ≫ F.rightIntermediateImageMap G H)
        (fundamentalCycle (F.rightFirstStageComponentExterior G H z)) := by
      rw [IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply]
    _ = IntegralCycle.finitePushforward
        (F.rightFirstStageComponentExteriorMap G H z ≫
          F.rightImageComponentExteriorInclusion G H
            (pointClosure ((G.incidenceMap H).toImage z.1)))
        (fundamentalCycle (F.rightFirstStageComponentExterior G H z)) :=
      hcongr _ _ inferInstance inferInstance
        (F.rightFirstStageComponentExteriorMap_ambient G H z).symm _
    _ = _ := by
      rw [IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply,
        rightFirstStageComponentExteriorMap_finitePushforward_fundamentalCycle, map_zsmul]

/-- The existing original right exterior cycle pushes to the full signed,
original-degree sum. Distinct original labels remain even when image supports collide. -/
theorem rightFirstStageOriginalExteriorCycle_finitePushforward_eq_imageExteriorSum :
    letI := IntegralCycle.genericPointFintype (G.incidence H)
    IntegralCycle.finitePushforward (F.rightIntermediateImageMap G H)
        (F.rightFirstStageOriginalExteriorCycle G H) =
      ∑ z : genericPoints (G.incidence H),
        (G.incidenceTorCoefficient (S := Spec (.of k)) H z *
          ((G.incidenceMap H).residueDegree z.1 : ℤ)) •
          IntegralCycle.finitePushforward
            (F.rightImageComponentExteriorInclusion G H
              (pointClosure ((G.incidenceMap H).toImage z.1)))
            (fundamentalCycle (F.rightImageComponentExterior G H
              (pointClosure ((G.incidenceMap H).toImage z.1)))) := by
  classical
  let := IntegralCycle.genericPointFintype (G.incidence H)
  rw [rightFirstStageOriginalExteriorCycle, map_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [map_zsmul, rightFirstStageComponentExterior_finitePushforward_ambient, smul_smul]

end Motivic.FiniteCorrespondenceGenerator
