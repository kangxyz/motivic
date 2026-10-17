/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.IntegralExteriorCyclePushforward
public import Motivic.AlgebraicGeometry.Correspondences.ExteriorImageGeneric
public import MotivicTest.IntegralExteriorDegreeLength

/-!
# Actual pair-exterior global cycle realization over arbitrary fields

For each original pair-incidence generic point, the actual pairExteriorMap
pushes the ENTIRE nonreduced exterior fundamental cycle to the original
incidence residue degree times the ENTIRE imageExterior fundamental cycle.

Generic preservation is proved for this specific map. The reduced pair
component has a finite source projection onto F's original smooth component.
Its actual exterior base change to X × H is generalizing by normality of X,
with the locally finite-type test map derived from SmoothSite geometry.
The exterior image-support projection to X × H is finite, so reflects generic
points. Neither the image support nor its exterior is assumed normal.

The final finite sum weights every original pair generic point by its actual
signed Tor coefficient and pushes via the actual imageExteriorInclusion.
All coincident image supports remain in the sum and add with their true
multiplicities. This is the exterior cycle realization step, not an iterated
pairing identification or a final correspondence associativity theorem.

SOURCE-ONLY: no compilation or prerequisite acceptance is claimed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open MotivicTest.IntegralGenericFiniteImage MotivicTest.IntegralExteriorResidueTensor
open MotivicTest.IntegralExteriorDegreeLength
open Motivic.IntegralExteriorCyclePushforward

universe u

namespace MotivicTest.IntegralExteriorCyclePushforward

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)
  (z : genericPoints (F.incidence G))

local instance cyclePushforward_consumerPairToImageFinite :
    IsFinite (F.incidenceMap G).toImage := F.incidenceToImage_isFinite G

/-- The reduced component's ORIGINAL source map, before exterior base change. -/
abbrev pairSupportSource : (pairSupport F G z).val.subscheme ⟶ X.left :=
  (pairSupport F G z).val.subschemeι ≫ F.incidenceSource G

local instance cyclePushforward_pairSupportSourceFinite : IsFinite (pairSupportSource F G z) := by
  dsimp only [pairSupportSource]
  infer_instance

/-- The component source projection has exactly F's specified source component
as its image; this uses actual incidence-component dominance. -/
theorem pairSupportSource_range :
    Set.range (pairSupportSource F G z) = Set.range F.projection :=
  F.range_incidence_component_source k G z

/-- The component's source and target structure maps are literally the same
map to the original field base. -/
@[reassoc] theorem pairSupportSource_structure :
    pairSupportSource F G z ≫ X.hom =
      (pairSupport F G z).val.subschemeι ≫ pairStructure F G := by
  simp only [pairSupportSource, pairStructure, Category.assoc, F.incidence_base G]

/-- The whole source-support exterior projects to the actual X × H. -/
def pairExteriorSource : pairExterior F G H z ⟶ pullback X.hom (H.projection ≫ Z.hom) :=
  pullback.lift
    (pullback.fst ((pairSupport F G z).val.subschemeι ≫ pairStructure F G)
      (H.projection ≫ Z.hom) ≫ pairSupportSource F G z)
    (pullback.snd ((pairSupport F G z).val.subschemeι ≫ pairStructure F G)
      (H.projection ≫ Z.hom)) (by
        rw [Category.assoc, pairSupportSource_structure]
        exact pullback.condition)

/-- The first projection retains the original pair component's source map. -/
@[reassoc (attr := simp)] theorem pairExteriorSource_fst :
    pairExteriorSource F G H z ≫ pullback.fst X.hom (H.projection ≫ Z.hom) =
      pullback.fst ((pairSupport F G z).val.subschemeι ≫ pairStructure F G)
        (H.projection ≫ Z.hom) ≫ pairSupportSource F G z :=
  pullback.lift_fst _ _ _

/-- The third correspondence support is literally unchanged. -/
@[reassoc (attr := simp)] theorem pairExteriorSource_snd :
    pairExteriorSource F G H z ≫ pullback.snd X.hom (H.projection ≫ Z.hom) =
      pullback.snd ((pairSupport F G z).val.subschemeι ≫ pairStructure F G)
        (H.projection ≫ Z.hom) :=
  pullback.lift_snd _ _ _

/-- This source projection is the actual Cartesian base change over the
original smooth X, with no normality condition on an image support. -/
theorem pairExteriorSource_isPullback :
    IsPullback (pairExteriorSource F G H z)
      (pullback.fst ((pairSupport F G z).val.subschemeι ≫ pairStructure F G)
        (H.projection ≫ Z.hom))
      (pullback.fst X.hom (H.projection ≫ Z.hom)) (pairSupportSource F G z) := by
  apply IsPullback.flip
  refine IsPullback.of_bot
    (t := IsPullback.of_hasPullback X.hom (H.projection ≫ Z.hom)) ?_
    (pairExteriorSource_fst F G H z).symm
  simpa only [pairExteriorSource_snd, pairSupportSource_structure] using
    (IsPullback.of_hasPullback
      ((pairSupport F G z).val.subschemeι ≫ pairStructure F G) (H.projection ≫ Z.hom))

/-- The test map to the original smooth source is locally finite type. -/
theorem pairExteriorSource_test_locallyOfFiniteType :
    LocallyOfFiniteType (pullback.fst X.hom (H.projection ≫ Z.hom)) := by
  infer_instance

/-- Genuine generalization lifting is derived from the finite integral pair
component, its component range, and normal stalks of the ORIGINAL smooth source. -/
theorem pairExteriorSource_generalizing : GeneralizingMap (pairExteriorSource F G H z) := by
  let cyclePushforward_testFiniteType := pairExteriorSource_test_locallyOfFiniteType (X := X) H
  let cyclePushforward_normalBaseNoetherian : IsNoetherian ((𝟭 Scheme).obj X.left) :=
    inferInstanceAs (IsNoetherian X.left)
  apply generalizingMap_of_isPullback_component _ _ _ _
    (pairExteriorSource_isPullback F G H z)
  · exact (congrArg (fun s : Set X.left => s ∈ irreducibleComponents X.left)
      (pairSupportSource_range F G z)).mpr F.range_projection_mem
  · intro x
    exact ⟨SmoothSite.isDomain_stalk k X x, SmoothSite.isIntegrallyClosed_stalk k X x⟩

/-- The source exterior's literal inclusion commutes with the previously
constructed whole exterior-source projection. -/
@[reassoc] theorem pairExteriorInclusion_source :
    pairExteriorInclusion F G H z ≫ F.leftExteriorSourceMap G H =
      pairExteriorSource F G H z := by
  apply pullback.hom_ext
  · simp only [FiniteCorrespondenceGenerator.leftExteriorSourceMap, Category.assoc,
      FiniteCorrespondenceGenerator.leftExteriorFirstSourceMap_fst,
      FiniteCorrespondenceGenerator.leftExteriorFirstSupportMap_fst_assoc,
      pairExteriorInclusion, IntegralClosedSubscheme.exteriorInclusion_fst_assoc,
      pairExteriorSource_fst, pairSupportSource,
      FiniteCorrespondenceGenerator.incidenceSource]
  · simp only [FiniteCorrespondenceGenerator.leftExteriorSourceMap, Category.assoc,
      FiniteCorrespondenceGenerator.leftExteriorFirstSourceMap_snd,
      FiniteCorrespondenceGenerator.leftExteriorFirstSupportMap_snd,
      pairExteriorInclusion, IntegralClosedSubscheme.exteriorInclusion_snd,
      pairExteriorSource_snd]

/-- The image-support exterior uses its actual closed immersion followed by
the whole intermediate image's original-source projection. -/
abbrev imageExteriorSource : imageExterior F G H z ⟶ pullback X.hom (H.projection ≫ Z.hom) :=
  imageExteriorInclusion F G H z ≫ F.leftExteriorImageSourceMap G H

/-- The target-support projection is finite, by its literal closed immersion
and the proved finite whole-image projection. -/
local instance cyclePushforward_imageExteriorSourceFinite :
    IsFinite (imageExteriorSource F G H z) := by
  let cyclePushforward_wholeImageSourceFinite := F.isFinite_leftExteriorImageSourceMap k G H
  dsimp only [imageExteriorSource]
  infer_instance

/-- The actual pair exterior map commutes with the two original-source maps. -/
@[reassoc] theorem pairExteriorMap_source :
    pairExteriorMap F G H z ≫ imageExteriorSource F G H z = pairExteriorSource F G H z := by
  dsimp only [imageExteriorSource]
  rw [← Category.assoc, pairExteriorMap_ambient, Category.assoc,
    F.leftIntermediateImageMap_source G H, pairExteriorInclusion_source]

/-- The ACTUAL pairExteriorMap preserves generic points. The normal-component
projection provides genericity downstairs, and the finite target projection
reflects it. No generic-preservation premise is supplied by this consumer. -/
theorem actualPairExterior_mem_genericPoints (w : genericPoints (pairExterior F G H z)) :
    pairExteriorMap F G H z w.1 ∈ genericPoints (imageExterior F G H z) := by
  apply mem_genericPoints_of_image_generic (imageExteriorSource F G H z)
  change (pairExteriorMap F G H z ≫ imageExteriorSource F G H z) w.1 ∈ _
  rw [pairExteriorMap_source]
  exact mem_genericPoints_of_generalizing _ (pairExteriorSource_generalizing F G H z) w.1 w.2

/-- The actual exterior base X × H is Noetherian, by finite type over X. -/
local instance cyclePushforward_sourceExteriorBaseNoetherian :
    IsNoetherian (pullback X.hom (H.projection ≫ Z.hom)) := by
  let : IsNoetherian ((𝟭 Scheme).obj X.left) := inferInstanceAs (IsNoetherian X.left)
  exact isNoetherian_of_finiteType (pullback.fst X.hom (H.projection ≫ Z.hom))

/-- The entire target-support exterior is Noetherian via its actual finite
projection. No reduced or integral replacement is made. -/
local instance cyclePushforward_imageExteriorNoetherian : IsNoetherian (imageExterior F G H z) :=
  isNoetherian_of_finiteType (imageExteriorSource F G H z)

/-- The entire source-support exterior is Noetherian via the actual finite
pairExteriorMap to the actual image-support exterior. -/
local instance cyclePushforward_pairExteriorNoetherian : IsNoetherian (pairExterior F G H z) :=
  isNoetherian_of_finiteType (pairExteriorMap F G H z)

/-- All nongeneric coefficients of the ACTUAL pushed exterior fundamental
cycle vanish, by the proved specific generic-preservation theorem. -/
theorem actualPairExterior_pushforward_eq_zero_of_not_generic
    (v : imageExterior F G H z) (hv : v ∉ genericPoints (imageExterior F G H z)) :
    IntegralCycle.toPoints
      (IntegralCycle.finitePushforward (pairExteriorMap F G H z)
        (fundamentalCycle (pairExterior F G H z))) v = 0 :=
  toPoints_finitePushforward_fundamentalCycle_eq_zero_of_not_generic
    (pairExteriorMap F G H z) (actualPairExterior_mem_genericPoints F G H z) v hv

/-- GLOBAL finite pushforward of the actual nonreduced pair-support exterior:
its degree is the original incidence degree, and every target generic stalk's
full nilpotent multiplicity is retained. This is equality of integral cycles. -/
theorem actualPairExterior_pushforward_fundamentalCycle :
    IntegralCycle.finitePushforward (pairExteriorMap F G H z)
        (fundamentalCycle (pairExterior F G H z)) =
      ((F.incidenceMap G).residueDegree z.1 : ℤ) • fundamentalCycle (imageExterior F G H z) := by
  have h := finitePushforward_fundamentalCycle_pointClosure_baseChange
    (F.incidenceMap G).toImage z.1 (pairExteriorMap_isPullback F G H z)
    (actualPairExterior_mem_genericPoints F G H z) (targetProjection_generic F G H z)
  rwa [actualPairToImage_residueDegree F G z] at h

/-- The integral support in the whole image becomes exactly the original
smooth incidence component generator after its actual image inclusion. -/
theorem imageSupport_ambient_eq_smoothIncidenceComponent :
    (imageSupport F G z).finiteImage (F.incidenceMap G).imageι =
      (F.smoothIncidenceComponentGenerator k G z).toIntegralClosedSubscheme := by
  rw [FiniteCorrespondenceGenerator.toIntegralClosedSubscheme_smoothIncidenceComponentGenerator]
  apply IntegralClosedSubscheme.point_injective
  simp only [IntegralClosedSubscheme.point_finiteImage, imageSupport,
    IntegralClosedSubscheme.point_pointClosure]
  exact congrArg (fun m => m z.1) (F.incidenceMap G).toImage_imageι

/-- After the actual support inclusions, functorial finite pushforward gives
the same global realization inside the WHOLE intermediate image exterior. -/
theorem actualPairExterior_pushforward_ambient :
    IntegralCycle.finitePushforward (F.leftIntermediateImageMap G H)
        (IntegralCycle.finitePushforward (pairExteriorInclusion F G H z)
          (fundamentalCycle (pairExterior F G H z))) =
      ((F.incidenceMap G).residueDegree z.1 : ℤ) •
        IntegralCycle.finitePushforward (imageExteriorInclusion F G H z)
          (fundamentalCycle (imageExterior F G H z)) := by
  calc
    _ = IntegralCycle.finitePushforward
        (pairExteriorInclusion F G H z ≫ F.leftIntermediateImageMap G H)
        (fundamentalCycle (pairExterior F G H z)) := by
      rw [IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply]
    _ = IntegralCycle.finitePushforward
        (pairExteriorMap F G H z ≫ imageExteriorInclusion F G H z)
        (fundamentalCycle (pairExterior F G H z)) := by
      have hcongr {A B : Scheme.{u}} (f g : A ⟶ B) (hf : IsFinite f)
          (hg : IsFinite g) (h : f = g) (c : IntegralCycle A) :
          @IntegralCycle.finitePushforward A B f hf c =
            @IntegralCycle.finitePushforward A B g hg c := by
        cases h
        rfl
      exact hcongr
        (pairExteriorInclusion F G H z ≫ F.leftIntermediateImageMap G H)
        (pairExteriorMap F G H z ≫ imageExteriorInclusion F G H z)
        inferInstance inferInstance (pairExteriorMap_ambient F G H z).symm
        (fundamentalCycle (pairExterior F G H z))
    _ = IntegralCycle.finitePushforward (imageExteriorInclusion F G H z)
        (IntegralCycle.finitePushforward (pairExteriorMap F G H z)
          (fundamentalCycle (pairExterior F G H z))) := by
      rw [IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply]
    _ = _ := by rw [actualPairExterior_pushforward_fundamentalCycle, map_zsmul]

/-- Signed original pair Tor coefficients weight the full global exterior
realization, with the original incidence residue degree. -/
theorem actualPairTorExterior_pushforward_ambient :
    IntegralCycle.finitePushforward (F.leftIntermediateImageMap G H)
        (F.incidenceTorCoefficient (S := Spec (.of k)) G z •
          IntegralCycle.finitePushforward (pairExteriorInclusion F G H z)
            (fundamentalCycle (pairExterior F G H z))) =
      (F.incidenceTorCoefficient (S := Spec (.of k)) G z *
        ((F.incidenceMap G).residueDegree z.1 : ℤ)) •
          IntegralCycle.finitePushforward (imageExteriorInclusion F G H z)
            (fundamentalCycle (imageExterior F G H z)) := by
  rw [map_zsmul, actualPairExterior_pushforward_ambient, smul_smul]

/-- The finite sum over ALL original pair-incidence generics realizes the
signed pair-Tor exterior cycle in the actual whole intermediate image product.
Distinct original points with the same image are retained and add; target
exterior fundamental multiplicities are never replaced by one. -/
theorem actualPairTorExterior_pushforward_sum :
    letI := IntegralCycle.genericPointFintype (F.incidence G)
    IntegralCycle.finitePushforward (F.leftIntermediateImageMap G H)
        (∑ z : genericPoints (F.incidence G),
          F.incidenceTorCoefficient (S := Spec (.of k)) G z •
            IntegralCycle.finitePushforward (pairExteriorInclusion F G H z)
              (fundamentalCycle (pairExterior F G H z))) =
      ∑ z : genericPoints (F.incidence G),
        (F.incidenceTorCoefficient (S := Spec (.of k)) G z *
          ((F.incidenceMap G).residueDegree z.1 : ℤ)) •
            IntegralCycle.finitePushforward (imageExteriorInclusion F G H z)
              (fundamentalCycle (imageExterior F G H z)) := by
  classical
  let cyclePushforward_pairGenericFintype := IntegralCycle.genericPointFintype (F.incidence G)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro z _
  exact actualPairTorExterior_pushforward_ambient F G H z

end MotivicTest.IntegralExteriorCyclePushforward
