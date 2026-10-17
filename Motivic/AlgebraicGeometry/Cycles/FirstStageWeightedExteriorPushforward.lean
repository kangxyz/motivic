/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.IntegralExteriorCyclePushforward
public import Motivic.AlgebraicGeometry.Cycles.WholeFiberTorExteriorPushforward
public import Motivic.AlgebraicGeometry.Correspondences.ExteriorImageComponentGeometry

/-!
# Actual degree-weighted first-stage exterior pushforward

The literal exterior base change of each original incidence point-closure map
pushes its whole fundamental cycle to the original incidence residue degree
times the whole image-support exterior fundamental cycle. Generic preservation
comes from the proved original-component inclusion and whole intermediate-image
map, followed by reflection through the actual closed image-support inclusion.

The final equality pushes the existing `firstStageOriginalExteriorCycle` to a
sum over every original incidence generic point. Signed Tor weights, coincident
image supports, all exterior branches, and nonreduced multiplicities remain.
All finiteness, Noetherianity and flatness are derived over an arbitrary field.
No remaining-diagonal, iterated-composition or associativity claim is made.

Prepared as a source-only candidate. Compilation and acceptance are recorded
separately; source presence alone certifies neither.
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
open ExteriorImageComponentGeometry

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

local instance weightedExterior_toImageFinite : IsFinite (F.incidenceMap G).toImage :=
  F.incidenceToImage_isFinite G

local instance weightedExterior_factorFlat : Flat (H.projection ≫ Z.hom) := by
  let : Subsingleton (Spec (.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  let : IsIntegral (Spec (.of k)) := inferInstance
  exact Flat.instOfSubsingletonCarrierCarrierCommRingCatOfIsIntegral
    (Y := Spec (.of k)) (H.projection ≫ Z.hom)

local instance weightedExterior_sourceNoetherian :
    IsNoetherian (F.leftIntermediateSupportProduct G H) :=
  isNoetherian_of_finiteType
    (pullback.fst (F.incidenceTarget G ≫ Z.hom) (H.projection ≫ Z.hom))

local instance weightedExterior_sourceBaseNoetherian :
    IsNoetherian (pullback X.hom (H.projection ≫ Z.hom)) := by
  let : IsNoetherian ((𝟭 Scheme).obj X.left) := inferInstanceAs (IsNoetherian X.left)
  exact isNoetherian_of_finiteType (pullback.fst X.hom (H.projection ≫ Z.hom))

local instance weightedExterior_imageProjectionFinite :
    IsFinite (F.leftExteriorImageSourceMap G H) :=
  F.isFinite_leftExteriorImageSourceMap k G H

local instance weightedExterior_imageNoetherian :
    IsNoetherian (F.leftIntermediateImageProduct G H) :=
  isNoetherian_of_finiteType (F.leftExteriorImageSourceMap G H)

local instance weightedExterior_sourceComponentNoetherian
    (z : genericPoints (F.incidence G)) :
    IsNoetherian (componentExterior (F.incidenceTarget G ≫ Z.hom)
      (H.projection ≫ Z.hom) z) :=
  isNoetherian_of_finiteType
    (componentExteriorInclusion (F.incidenceTarget G ≫ Z.hom) (H.projection ≫ Z.hom) z)

local instance weightedExterior_imageComponentNoetherian
    (C : IntegralClosedSubscheme (F.incidenceMap G).image) :
    IsNoetherian (exterior F G H C) :=
  isNoetherian_of_finiteType (ExteriorImageComponentGeometry.exteriorInclusion F G H C)

variable (z : genericPoints (F.incidence G))

/-- The point-closure map preserves the literal structure map to the field base. -/
@[reassoc] theorem firstStagePointClosureMap_structure :
    pointClosureMap (F.incidenceMap G).toImage z.1 ≫
        (pointClosure ((F.incidenceMap G).toImage z.1)).val.subschemeι ≫
        (F.incidenceMap G).imageι ≫ pullback.snd X.hom Z.hom ≫ Z.hom =
      (pointClosure z.1).val.subschemeι ≫ F.incidenceTarget G ≫ Z.hom := by
  simp only [pointClosureMap_ambient_assoc, Scheme.Hom.toImage_imageι_assoc,
    incidenceMap_snd_assoc]
  simp only [incidenceTarget, targetProjection, Category.assoc]

/-- The actual exterior base change, with the original source and image supports. -/
def firstStageComponentExteriorMap :
    componentExterior (F.incidenceTarget G ≫ Z.hom) (H.projection ≫ Z.hom) z ⟶
      ExteriorImageComponentGeometry.exterior F G H
        (pointClosure ((F.incidenceMap G).toImage z.1)) :=
  pullback.map _ _ _ _ (pointClosureMap (F.incidenceMap G).toImage z.1)
    (𝟙 H.scheme) (𝟙 (Spec (.of k)))
    ((Category.comp_id
      ((pointClosure z.1).val.subschemeι ≫ F.incidenceTarget G ≫ Z.hom :
        (pointClosure z.1).val.subscheme ⟶ Spec (.of k))).trans
      (F.firstStagePointClosureMap_structure G z).symm) (by simp)

/-- Its first projection is the original point-closure map. -/
@[reassoc (attr := simp)] theorem firstStageComponentExteriorMap_fst :
    F.firstStageComponentExteriorMap G H z ≫
        pullback.fst ((pointClosure ((F.incidenceMap G).toImage z.1)).val.subschemeι ≫
          (F.incidenceMap G).imageι ≫
          pullback.snd X.hom Z.hom ≫ Z.hom) (H.projection ≫ Z.hom) =
      pullback.fst ((pointClosure z.1).val.subschemeι ≫ F.incidenceTarget G ≫ Z.hom)
        (H.projection ≫ Z.hom) ≫ pointClosureMap (F.incidenceMap G).toImage z.1 :=
  pullback.lift_fst _ _ _

/-- The third correspondence support remains literally unchanged. -/
@[reassoc (attr := simp)] theorem firstStageComponentExteriorMap_snd :
    F.firstStageComponentExteriorMap G H z ≫
        pullback.snd ((pointClosure ((F.incidenceMap G).toImage z.1)).val.subschemeι ≫
          (F.incidenceMap G).imageι ≫
          pullback.snd X.hom Z.hom ≫ Z.hom) (H.projection ≫ Z.hom) =
      pullback.snd ((pointClosure z.1).val.subschemeι ≫ F.incidenceTarget G ≫ Z.hom)
        (H.projection ≫ Z.hom) := by
  simp only [firstStageComponentExteriorMap, pullback.map, pullback.lift_snd, Category.comp_id]

/-- The whole exterior map is Cartesian over the actual finite point-closure map. -/
theorem firstStageComponentExteriorMap_isPullback :
    IsPullback
      (pullback.fst ((pointClosure z.1).val.subschemeι ≫ F.incidenceTarget G ≫ Z.hom)
        (H.projection ≫ Z.hom))
      (F.firstStageComponentExteriorMap G H z)
      (pointClosureMap (F.incidenceMap G).toImage z.1)
      (pullback.fst ((pointClosure ((F.incidenceMap G).toImage z.1)).val.subschemeι ≫
          (F.incidenceMap G).imageι ≫
        pullback.snd X.hom Z.hom ≫ Z.hom) (H.projection ≫ Z.hom)) := by
  refine IsPullback.of_bot
    (t := IsPullback.of_hasPullback
      ((pointClosure ((F.incidenceMap G).toImage z.1)).val.subschemeι ≫
        (F.incidenceMap G).imageι ≫ pullback.snd X.hom Z.hom ≫ Z.hom)
      (H.projection ≫ Z.hom)) ?_ (F.firstStageComponentExteriorMap_fst G H z).symm
  simpa only [firstStageComponentExteriorMap_snd, firstStagePointClosureMap_structure] using
    (IsPullback.of_hasPullback ((pointClosure z.1).val.subschemeι ≫ F.incidenceTarget G ≫ Z.hom)
      (H.projection ≫ Z.hom))

/-- Finiteness follows from the literal Cartesian square. -/
local instance firstStageComponentExteriorMap_isFinite :
    IsFinite (F.firstStageComponentExteriorMap G H z) :=
  MorphismProperty.of_isPullback (F.firstStageComponentExteriorMap_isPullback G H z)
    inferInstance

/-- Both support inclusions commute with the original whole intermediate-image map. -/
@[reassoc] theorem firstStageComponentExteriorMap_ambient :
    F.firstStageComponentExteriorMap G H z ≫
        ExteriorImageComponentGeometry.exteriorInclusion F G H
          (pointClosure ((F.incidenceMap G).toImage z.1)) =
      componentExteriorInclusion (F.incidenceTarget G ≫ Z.hom)
        (H.projection ≫ Z.hom) z ≫ F.leftIntermediateImageMap G H := by
  apply pullback.hom_ext
  · simp only [Category.assoc, ExteriorImageComponentGeometry.exteriorInclusion,
      componentExteriorInclusion,
      IntegralClosedSubscheme.exteriorInclusion_fst, firstStageComponentExteriorMap_fst_assoc,
      leftIntermediateImageMap_fst, IntegralClosedSubscheme.exteriorInclusion_fst_assoc,
      pointClosureMap_ambient]
  · simp only [Category.assoc, ExteriorImageComponentGeometry.exteriorInclusion,
      componentExteriorInclusion,
      IntegralClosedSubscheme.exteriorInclusion_snd, firstStageComponentExteriorMap_snd,
      leftIntermediateImageMap_snd]

/-- Generic preservation uses the proved whole-map geometry and the actual closed inclusion. -/
theorem firstStageComponentExteriorMap_mem_genericPoints
    (w : genericPoints (componentExterior (F.incidenceTarget G ≫ Z.hom)
      (H.projection ≫ Z.hom) z)) :
    F.firstStageComponentExteriorMap G H z w.1 ∈
      genericPoints (ExteriorImageComponentGeometry.exterior F G H
        (pointClosure ((F.incidenceMap G).toImage z.1))) := by
  apply mem_genericPoints_of_image_generic
    (ExteriorImageComponentGeometry.exteriorInclusion F G H
      (pointClosure ((F.incidenceMap G).toImage z.1)))
  change (F.firstStageComponentExteriorMap G H z ≫
    ExteriorImageComponentGeometry.exteriorInclusion F G H
      (pointClosure ((F.incidenceMap G).toImage z.1))) w.1 ∈ _
  rw [firstStageComponentExteriorMap_ambient, Scheme.Hom.comp_apply]
  exact F.leftIntermediateImageMap_mem_genericPoints k G H _
    (componentExterior_generic_mem (F.incidenceTarget G ≫ Z.hom) (H.projection ≫ Z.hom) z w)

/-- Every image-exterior generic projects to the original integral support generic. -/
theorem firstStageImageExterior_projection_generic
    (v : genericPoints (ExteriorImageComponentGeometry.exterior F G H
        (pointClosure ((F.incidenceMap G).toImage z.1)))) :
    pullback.fst ((pointClosure ((F.incidenceMap G).toImage z.1)).val.subschemeι ≫
          (F.incidenceMap G).imageι ≫
        pullback.snd X.hom Z.hom ≫ Z.hom) (H.projection ≫ Z.hom) v.1 =
      genericPoint (pointClosure ((F.incidenceMap G).toImage z.1)).val.subscheme :=
  (pointClosure ((F.incidenceMap G).toImage z.1)).exteriorGeneric_projection
    ((F.incidenceMap G).imageι ≫ pullback.snd X.hom Z.hom ≫ Z.hom)
    (H.projection ≫ Z.hom) v

/-- Passing through the whole scheme image retains the original incidence residue degree. -/
theorem firstStageToImage_residueDegree :
    (F.incidenceMap G).toImage.residueDegree z.1 = (F.incidenceMap G).residueDegree z.1 := by
  have he := congrArg (fun m => m.residueDegree z.1) (F.incidenceMap G).toImage_imageι
  simpa only [residueDegree_comp, residueDegree_of_surjectiveOnStalks, one_mul] using he

/-- The full global component identity retains all branches and nilpotent multiplicities. -/
theorem firstStageComponentExteriorMap_finitePushforward_fundamentalCycle :
    IntegralCycle.finitePushforward (F.firstStageComponentExteriorMap G H z)
        (fundamentalCycle (componentExterior (F.incidenceTarget G ≫ Z.hom)
          (H.projection ≫ Z.hom) z)) =
      ((F.incidenceMap G).residueDegree z.1 : ℤ) •
        fundamentalCycle (ExteriorImageComponentGeometry.exterior F G H
          (pointClosure ((F.incidenceMap G).toImage z.1))) := by
  have h :=
    IntegralExteriorCyclePushforward.finitePushforward_fundamentalCycle_pointClosure_baseChange
      (F.incidenceMap G).toImage z.1 (F.firstStageComponentExteriorMap_isPullback G H z)
      (F.firstStageComponentExteriorMap_mem_genericPoints G H z)
      (F.firstStageImageExterior_projection_generic G H z)
  rwa [firstStageToImage_residueDegree] at h

/-- The same component identity in the actual whole intermediate-image exterior. -/
theorem firstStageComponentExterior_finitePushforward_ambient :
    IntegralCycle.finitePushforward (F.leftIntermediateImageMap G H)
        (IntegralCycle.finitePushforward
          (componentExteriorInclusion (F.incidenceTarget G ≫ Z.hom) (H.projection ≫ Z.hom) z)
          (fundamentalCycle (componentExterior (F.incidenceTarget G ≫ Z.hom)
            (H.projection ≫ Z.hom) z))) =
      ((F.incidenceMap G).residueDegree z.1 : ℤ) •
        IntegralCycle.finitePushforward
          (ExteriorImageComponentGeometry.exteriorInclusion F G H
            (pointClosure ((F.incidenceMap G).toImage z.1)))
          (fundamentalCycle (ExteriorImageComponentGeometry.exterior F G H
            (pointClosure ((F.incidenceMap G).toImage z.1)))) := by
  calc
    _ = IntegralCycle.finitePushforward
        (componentExteriorInclusion (F.incidenceTarget G ≫ Z.hom) (H.projection ≫ Z.hom) z ≫
          F.leftIntermediateImageMap G H)
        (fundamentalCycle (componentExterior (F.incidenceTarget G ≫ Z.hom)
          (H.projection ≫ Z.hom) z)) := by
      rw [IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply]
    _ = IntegralCycle.finitePushforward
        (F.firstStageComponentExteriorMap G H z ≫
          ExteriorImageComponentGeometry.exteriorInclusion F G H
            (pointClosure ((F.incidenceMap G).toImage z.1)))
        (fundamentalCycle (componentExterior (F.incidenceTarget G ≫ Z.hom)
          (H.projection ≫ Z.hom) z)) := by
      have hcongr {A B : Scheme.{u}} (f g : A ⟶ B) (hf : IsFinite f)
          (hg : IsFinite g) (h : f = g) (c : IntegralCycle A) :
          @IntegralCycle.finitePushforward A B f hf c =
            @IntegralCycle.finitePushforward A B g hg c := by
        cases h
        rfl
      exact hcongr _ _ inferInstance inferInstance
        (F.firstStageComponentExteriorMap_ambient G H z).symm
        (fundamentalCycle (componentExterior (F.incidenceTarget G ≫ Z.hom)
          (H.projection ≫ Z.hom) z))
    _ = IntegralCycle.finitePushforward
        (ExteriorImageComponentGeometry.exteriorInclusion F G H
          (pointClosure ((F.incidenceMap G).toImage z.1)))
        (IntegralCycle.finitePushforward (F.firstStageComponentExteriorMap G H z)
          (fundamentalCycle (componentExterior (F.incidenceTarget G ≫ Z.hom)
            (H.projection ≫ Z.hom) z))) := by
      rw [IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply]
    _ = _ := by
      rw [firstStageComponentExteriorMap_finitePushforward_fundamentalCycle, map_zsmul]

/-- The existing original exterior cycle pushes to the full original-degree image sum.
Every original label and signed Tor weight remains, including colliding image supports. -/
theorem firstStageOriginalExteriorCycle_finitePushforward_eq_imageExteriorSum :
    letI := IntegralCycle.genericPointFintype (F.incidence G)
    IntegralCycle.finitePushforward (F.leftIntermediateImageMap G H)
        (F.firstStageOriginalExteriorCycle G H) =
      ∑ z : genericPoints (F.incidence G),
        (F.incidenceTorCoefficient (S := Spec (.of k)) G z *
          ((F.incidenceMap G).residueDegree z.1 : ℤ)) •
          IntegralCycle.finitePushforward
            (ExteriorImageComponentGeometry.exteriorInclusion F G H
              (pointClosure ((F.incidenceMap G).toImage z.1)))
            (fundamentalCycle (ExteriorImageComponentGeometry.exterior F G H
              (pointClosure ((F.incidenceMap G).toImage z.1)))) := by
  classical
  let := IntegralCycle.genericPointFintype (F.incidence G)
  rw [firstStageOriginalExteriorCycle, map_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [map_zsmul, firstStageComponentExterior_finitePushforward_ambient, smul_smul]

end Motivic.FiniteCorrespondenceGenerator
