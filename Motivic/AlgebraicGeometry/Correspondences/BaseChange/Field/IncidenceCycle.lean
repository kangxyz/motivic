/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.BaseChange.Field.Incidence
public import Motivic.AlgebraicGeometry.Correspondences.BaseChange.Field.Pushforward
public import Motivic.AlgebraicGeometry.Correspondences.BaseChange.Field.Graph
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.RightWholeFiberTorExteriorDecomposition

/-!
# Actual incidence-cycle assembly under arbitrary field change

The entire new incidence is partitioned by original incidence components before
finite pushforward. All closed-fiber multiplicities and signed Tor coefficients
are retained, including nongeneric vanishing and colliding finite images.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

universe u

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme

open _root_.AlgebraicGeometry.Scheme.Cycles.BaseChange.ComponentDecomposition
open RightWholeFiberTorExteriorDecomposition

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L)
  {X Y Z : SmoothSite.overField k} (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)

private theorem fieldBaseChangeProjection_hom :
    A.fieldBaseChangeProjection φ ≫ ((SmoothSite.fieldBaseChange φ).obj X).hom =
      A.fieldBaseChangeSupportHom φ := A.fieldBaseChangeProjection_snd φ

/-- The whole new incidence maps to the actual new source-target product. -/
def fieldBaseChangeIncidenceMap : A.fieldBaseChangeIncidence φ B ⟶
    (SmoothSite.product ((SmoothSite.fieldBaseChange φ).obj X)
      ((SmoothSite.fieldBaseChange φ).obj Z)).left :=
  pullback.lift
    (A.fieldBaseChangeIncidenceFst φ B ≫ A.fieldBaseChangeProjection φ)
    (A.fieldBaseChangeIncidenceSnd φ B ≫ B.fieldBaseChangeTargetProjection φ) (by
      simp only [Category.assoc, fieldBaseChangeTargetProjection_snd]
      rw [fieldBaseChangeProjection_hom]
      have h := congrArg (fun f => f ≫ ((SmoothSite.fieldBaseChange φ).obj Y).hom)
        (pullback.condition (f := A.fieldBaseChangeTargetProjection φ)
          (g := B.fieldBaseChangeProjection φ))
      simpa only [Category.assoc, fieldBaseChangeTargetProjection_snd,
        fieldBaseChangeProjection_hom] using h)

@[reassoc]
theorem fieldBaseChangeIncidenceMap_fst :
    A.fieldBaseChangeIncidenceMap φ B ≫
      pullback.fst ((SmoothSite.fieldBaseChange φ).obj X).hom
        ((SmoothSite.fieldBaseChange φ).obj Z).hom =
      A.fieldBaseChangeIncidenceFst φ B ≫ A.fieldBaseChangeProjection φ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem fieldBaseChangeIncidenceMap_fst_simp :
    A.fieldBaseChangeIncidenceMap φ B ≫
      pullback.fst (pullback.snd X.hom (Spec.map (CommRingCat.ofHom φ)))
        (pullback.snd Z.hom (Spec.map (CommRingCat.ofHom φ))) =
      A.fieldBaseChangeIncidenceFst φ B ≫ A.fieldBaseChangeProjection φ :=
  fieldBaseChangeIncidenceMap_fst φ A B

@[reassoc]
theorem fieldBaseChangeIncidenceMap_snd :
    A.fieldBaseChangeIncidenceMap φ B ≫
      pullback.snd ((SmoothSite.fieldBaseChange φ).obj X).hom
        ((SmoothSite.fieldBaseChange φ).obj Z).hom =
      A.fieldBaseChangeIncidenceSnd φ B ≫ B.fieldBaseChangeTargetProjection φ :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)] theorem fieldBaseChangeIncidenceMap_snd_simp :
    A.fieldBaseChangeIncidenceMap φ B ≫
      pullback.snd (pullback.snd X.hom (Spec.map (CommRingCat.ofHom φ)))
        (pullback.snd Z.hom (Spec.map (CommRingCat.ofHom φ))) =
      A.fieldBaseChangeIncidenceSnd φ B ≫ B.fieldBaseChangeTargetProjection φ :=
  fieldBaseChangeIncidenceMap_snd φ A B

instance fieldBaseChangeIncidenceMap_isFinite : IsFinite (A.fieldBaseChangeIncidenceMap φ B) := by
  have : IsFinite (A.fieldBaseChangeIncidenceMap φ B ≫
      pullback.fst ((SmoothSite.fieldBaseChange φ).obj X).hom
        ((SmoothSite.fieldBaseChange φ).obj Z).hom) := by
    rw [fieldBaseChangeIncidenceMap_fst]
    infer_instance
  exact IsFinite.of_comp (A.fieldBaseChangeIncidenceMap φ B)
    (pullback.fst ((SmoothSite.fieldBaseChange φ).obj X).hom
      ((SmoothSite.fieldBaseChange φ).obj Z).hom)

/-- The literal Cartesian presentation of the entire new incidence. -/
def fieldBaseChangeIncidencePullbackIso : A.fieldBaseChangeIncidence φ B ≅
    pullback (A.incidenceSource B ≫ X.hom) (Spec.map (CommRingCat.ofHom φ)) :=
  (A.fieldBaseChangeIncidence_isPullback φ B).isoPullback

@[reassoc (attr := simp)]
theorem fieldBaseChangeIncidencePullbackIso_inv_original :
    (A.fieldBaseChangeIncidencePullbackIso φ B).inv ≫
      A.fieldBaseChangeIncidenceToOriginal φ B =
        pullback.fst (A.incidenceSource B ≫ X.hom) (Spec.map (CommRingCat.ofHom φ)) :=
  (A.fieldBaseChangeIncidence_isPullback φ B).isoPullback_inv_fst

local instance fieldComposition_fieldFlat : Flat (Spec.map (CommRingCat.ofHom φ)) :=
  Flat.SpecMap_iff.mpr (RingHom.Flat.of_isField (Field.toIsField k) φ)

instance fieldBaseChangeIncidencePullback_isNoetherian :
    IsNoetherian (pullback (A.incidenceSource B ≫ X.hom)
      (Spec.map (CommRingCat.ofHom φ))) :=
  isNoetherian_of_finiteType (A.fieldBaseChangeIncidencePullbackIso φ B).inv

local instance fieldComposition_topNoetherian :
    IsNoetherian (⊤ : (pullback (A.incidenceSource B ≫ X.hom)
      (Spec.map (CommRingCat.ofHom φ)) : Scheme.{u}).Opens).toScheme :=
  isNoetherian_of_finiteType (Scheme.topIso _).hom

instance fieldBaseChangeIncidenceComponent_isNoetherian (x : genericPoints (A.incidence B)) :
    IsNoetherian (componentExterior (A.incidenceSource B ≫ X.hom)
      (Spec.map (CommRingCat.ofHom φ)) x) :=
  isNoetherian_of_finiteType (componentExteriorInclusion (A.incidenceSource B ≫ X.hom)
    (Spec.map (CommRingCat.ofHom φ)) x)

/-- The original projection stalk maps form the actual isomorphic arrows. -/
def fieldBaseChangeIncidenceProjectionStalkArrowIso
    (w : (pullback (A.incidenceSource B ≫ X.hom) (Spec.map (CommRingCat.ofHom φ)) : Scheme.{u})) :
    Arrow.mk ((A.fieldBaseChangeIncidenceToOriginal φ B).stalkMap
      ((A.fieldBaseChangeIncidencePullbackIso φ B).inv w)) ≅
    Arrow.mk ((pullback.fst (A.incidenceSource B ≫ X.hom)
      (Spec.map (CommRingCat.ofHom φ))).stalkMap w) :=
  Arrow.isoMk
    ((A.incidence B).presheaf.stalkCongr (.of_eq (congrArg
      (fun f : pullback (A.incidenceSource B ≫ X.hom)
        (Spec.map (CommRingCat.ofHom φ)) ⟶ A.incidence B => f w)
      (A.fieldBaseChangeIncidencePullbackIso_inv_original φ B))))
    (asIso ((A.fieldBaseChangeIncidencePullbackIso φ B).inv.stalkMap w)) (by
      dsimp only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom, asIso_hom]
      simpa only [Scheme.Hom.stalkMap_comp] using
        (Scheme.Hom.stalkMap_congr_hom
          ((A.fieldBaseChangeIncidencePullbackIso φ B).inv ≫
            A.fieldBaseChangeIncidenceToOriginal φ B)
          (pullback.fst (A.incidenceSource B ≫ X.hom) (Spec.map (CommRingCat.ofHom φ)))
          (A.fieldBaseChangeIncidencePullbackIso_inv_original φ B) w).symm)

private theorem fieldBaseChangeIncidenceTopGeneric_original
    (w : genericPoints (⊤ : (pullback (A.incidenceSource B ≫ X.hom)
      (Spec.map (CommRingCat.ofHom φ)) : Scheme.{u}).Opens).toScheme) :
    A.fieldBaseChangeIncidenceOriginalGeneric φ B
      (mapGenericPoint ((Scheme.topIso _).hom ≫
        (A.fieldBaseChangeIncidencePullbackIso φ B).inv) w) =
    componentGeneric (A.incidenceSource B ≫ X.hom)
      (Spec.map (CommRingCat.ofHom φ)) ⊤ w := by
  apply Subtype.ext
  exact congrArg (fun f : pullback (A.incidenceSource B ≫ X.hom)
    (Spec.map (CommRingCat.ofHom φ)) ⟶ A.incidence B => f w.1.1)
      (A.fieldBaseChangeIncidencePullbackIso_inv_original φ B)

private theorem fieldBaseChangeIncidenceTopGeneric_fiber
    (w : genericPoints (⊤ : (pullback (A.incidenceSource B ≫ X.hom)
      (Spec.map (CommRingCat.ofHom φ)) : Scheme.{u}).Opens).toScheme) :
    A.fieldBaseChangeIncidenceFiberMultiplicity φ B
      (mapGenericPoint ((Scheme.topIso _).hom ≫
        (A.fieldBaseChangeIncidencePullbackIso φ B).inv) w) =
    closedFiberMultiplicity (A.incidenceSource B ≫ X.hom)
      (Spec.map (CommRingCat.ofHom φ)) ⊤ w := by
  unfold fieldBaseChangeIncidenceFiberMultiplicity closedFiberMultiplicity
      _root_.HomologicalComplex.ModuleLengthEuler.integerLength
  exact congrArg (fun n : ℕ∞ => (n.toNat : ℤ))
    (closedFiberArrow_length (A.fieldBaseChangeIncidenceProjectionStalkArrowIso φ B w.1.1))

/-- Removing the top-open wrappers preserves every whole component multiplicity. -/
private theorem fieldBaseChangeIncidenceTop_component
    (x : genericPoints (A.incidence B)) :
    IntegralCycle.finitePushforward (Scheme.topIso _).hom
      (IntegralCycle.finitePushforward
        (componentInclusion (A.incidenceSource B ≫ X.hom)
          (Spec.map (CommRingCat.ofHom φ)) ⊤ x)
        (fundamentalCycle (componentOpen (A.incidenceSource B ≫ X.hom)
          (Spec.map (CommRingCat.ofHom φ)) ⊤ x))) =
    IntegralCycle.finitePushforward
      (componentExteriorInclusion (A.incidenceSource B ≫ X.hom)
        (Spec.map (CommRingCat.ofHom φ)) x)
      (fundamentalCycle (componentExterior (A.incidenceSource B ≫ X.hom)
        (Spec.map (CommRingCat.ofHom φ)) x)) := by
  let b := componentExteriorInclusion (A.incidenceSource B ≫ X.hom)
    (Spec.map (CommRingCat.ofHom φ)) x
  have : IsIso (b ⁻¹ᵁ ⊤).ι := by
    rw [Scheme.Hom.preimage_top]
    exact (Scheme.topIso _).isIso_hom
  have hmap : componentInclusion (A.incidenceSource B ≫ X.hom)
      (Spec.map (CommRingCat.ofHom φ)) ⊤ x ≫ (Scheme.topIso _).hom =
        (b ⁻¹ᵁ ⊤).ι ≫ b :=
    componentInclusion_ambient (A.incidenceSource B ≫ X.hom)
      (Spec.map (CommRingCat.ofHom φ)) ⊤ x
  have hcongr {D E : Scheme.{u}} (f g : D ⟶ E) (hf : IsFinite f) (hg : IsFinite g)
      (h : f = g) (c : IntegralCycle D) :
      @IntegralCycle.finitePushforward D E f hf c =
        @IntegralCycle.finitePushforward D E g hg c := by
    cases h
    rfl
  rw [← AddMonoidHom.comp_apply, ← IntegralCycle.finitePushforward_comp]
  refine (hcongr _ _ inferInstance inferInstance hmap _).trans ?_
  rw [IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply,
    finitePushforward_fundamentalCycle]

/-- The full original-component cycle decomposition, with arbitrary signed weights.
It is an equality of cycles at every point, not merely a generic comparison. -/
theorem fieldBaseChangeIncidenceCycle_eq_component_sum
    (c : genericPoints (A.incidence B) → ℤ) :
    IntegralCycle.ofGenericCoefficients (A.fieldBaseChangeIncidence φ B)
      (fun w => c (A.fieldBaseChangeIncidenceOriginalGeneric φ B w) *
        A.fieldBaseChangeIncidenceFiberMultiplicity φ B w) =
    letI := IntegralCycle.genericPointFintype (A.incidence B)
    IntegralCycle.finitePushforward (A.fieldBaseChangeIncidencePullbackIso φ B).inv
      (∑ x : genericPoints (A.incidence B), c x •
        IntegralCycle.finitePushforward
          (componentExteriorInclusion (A.incidenceSource B ≫ X.hom)
            (Spec.map (CommRingCat.ofHom φ)) x)
          (fundamentalCycle (componentExterior (A.incidenceSource B ≫ X.hom)
            (Spec.map (CommRingCat.ofHom φ)) x))) := by
  classical
  let := IntegralCycle.genericPointFintype (A.incidence B)
  let p := A.incidenceSource B ≫ X.hom
  let t := Spec.map (CommRingCat.ofHom φ)
  have hc := finitePushforward_genericCoefficients_iso
    ((Scheme.topIso _).hom ≫ (A.fieldBaseChangeIncidencePullbackIso φ B).inv)
    (fun w => c (componentGeneric p t ⊤ w) * closedFiberMultiplicity p t ⊤ w)
    (fun w => c (A.fieldBaseChangeIncidenceOriginalGeneric φ B w) *
      A.fieldBaseChangeIncidenceFiberMultiplicity φ B w) (fun w => by
        rw [A.fieldBaseChangeIncidenceTopGeneric_original φ B,
          A.fieldBaseChangeIncidenceTopGeneric_fiber φ B])
  rw [← hc, ofGenericCoefficients_eq_component_sum,
    IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply]
  apply congrArg (IntegralCycle.finitePushforward (A.fieldBaseChangeIncidencePullbackIso φ B).inv)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [map_zsmul, A.fieldBaseChangeIncidenceTop_component φ B x]

end Motivic.FiniteCorrespondenceGenerator
