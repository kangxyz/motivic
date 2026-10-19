/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.ScalarExtension.FlatFundamentalCycleTower
public import Motivic.Cohomology.SuslinVoevodsky.FieldCohomologyChange

/-!
# Geometric prerequisites for coherence of the actual field-change maps

The original whole support has a canonical identity comparison and a canonical
field-tower comparison. Its fundamental cycle is preserved by these literal
pullback isomorphisms. The composite-field cycle decomposes over every
intermediate component with that component's original generic length and its
whole second pullback. These are prerequisites for all-degree coherence of the
original raw and derived field-change maps; that coherence is not asserted here.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Cycles.BaseChange.ComponentDecomposition
open scoped BigOperators

universe u

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme

variable {k L M : Type u} [Field k] [Field L] [Field M]
  (φ : k →+* L) (ψ : L →+* M)
  {X Y : SmoothSite.overField k} (A : FiniteCorrespondenceGenerator X.hom Y.hom)

local instance fieldCoherence_source_isNoetherian : IsNoetherian ((𝟭 Scheme).obj X.left) :=
  inferInstanceAs (IsNoetherian X.left)

local instance fieldCoherence_scheme_isNoetherian : IsNoetherian A.scheme :=
  isNoetherian_of_finiteType A.projection

instance fieldBaseChangeSupportToOriginal_id_isIso :
    IsIso (A.fieldBaseChangeSupportToOriginal (RingHom.id k)) := by
  change IsIso (pullback.fst (A.projection ≫ X.hom)
    (Spec.map (CommRingCat.ofHom (RingHom.id k))))
  rw [CommRingCat.ofHom_id, Spec.map_id]
  infer_instance

/-- The whole identity-field support is compared by its original projection. -/
def fieldBaseChangeSupportIdIso : A.fieldBaseChangeSupport (RingHom.id k) ≅ A.scheme :=
  asIso (A.fieldBaseChangeSupportToOriginal (RingHom.id k))

@[simp]
theorem fieldBaseChangeSupportIdIso_hom :
    A.fieldBaseChangeSupportIdIso.hom =
      A.fieldBaseChangeSupportToOriginal (RingHom.id k) := rfl

/-- The identity comparison retains the full fundamental cycle. -/
theorem finitePushforward_fieldBaseChangeSupportId_fundamentalCycle :
    IntegralCycle.finitePushforward A.fieldBaseChangeSupportIdIso.hom
      (fundamentalCycle (A.fieldBaseChangeSupport (RingHom.id k))) =
        fundamentalCycle A.scheme :=
  finitePushforward_fundamentalCycle A.fieldBaseChangeSupportIdIso.hom

/-- The whole second pullback, before replacing any component by its reduction. -/
abbrev fieldBaseChangeTowerSupport : Scheme.{u} :=
  pullback (A.fieldBaseChangeSupportHom φ) (Spec.map (CommRingCat.ofHom ψ))

/-- The actual tower is compared with the original composite-field support by
pasting pullbacks and the literal contravariance equation for `Spec`. -/
def fieldBaseChangeSupportTowerIso :
    A.fieldBaseChangeTowerSupport φ ψ ≅ A.fieldBaseChangeSupport (ψ.comp φ) :=
  pullbackTowerIso (A.projection ≫ X.hom)
      (Spec.map (CommRingCat.ofHom φ)) (Spec.map (CommRingCat.ofHom ψ)) ≪≫
    pullback.congrHom rfl (by rw [← Spec.map_comp]; rfl)

/-- The canonical tower comparison retains both original source projections. -/
@[reassoc (attr := simp)]
theorem fieldBaseChangeSupportTowerIso_hom_original :
    (A.fieldBaseChangeSupportTowerIso φ ψ).hom ≫
        A.fieldBaseChangeSupportToOriginal (ψ.comp φ) =
      pullback.fst (A.fieldBaseChangeSupportHom φ) (Spec.map (CommRingCat.ofHom ψ)) ≫
        A.fieldBaseChangeSupportToOriginal φ := by
  simp [fieldBaseChangeSupportTowerIso, fieldBaseChangeSupportToOriginal,
    fieldBaseChangeSupportHom]

/-- The final field projection is the literal second pullback projection. -/
@[reassoc (attr := simp)]
theorem fieldBaseChangeSupportTowerIso_hom_base :
    (A.fieldBaseChangeSupportTowerIso φ ψ).hom ≫
        A.fieldBaseChangeSupportHom (ψ.comp φ) =
      pullback.snd (A.fieldBaseChangeSupportHom φ) (Spec.map (CommRingCat.ofHom ψ)) := by
  simp [fieldBaseChangeSupportTowerIso, fieldBaseChangeSupportHom]

/-- Noetherianity comes from the original composite-field support, without a
finite-type assumption on either field extension. -/
instance fieldBaseChangeTowerSupport_isNoetherian :
    IsNoetherian (A.fieldBaseChangeTowerSupport φ ψ) :=
  isNoetherian_of_finiteType (A.fieldBaseChangeSupportTowerIso φ ψ).hom

/-- The full tower fundamental cycle agrees with the full composite support's
fundamental cycle, including all inseparable multiplicities. -/
theorem finitePushforward_fieldBaseChangeSupportTower_fundamentalCycle :
    IntegralCycle.finitePushforward (A.fieldBaseChangeSupportTowerIso φ ψ).hom
      (fundamentalCycle (A.fieldBaseChangeTowerSupport φ ψ)) =
        fundamentalCycle (A.fieldBaseChangeSupport (ψ.comp φ)) :=
  finitePushforward_fundamentalCycle (A.fieldBaseChangeSupportTowerIso φ ψ).hom

/-- Every intermediate generic component contributes its original whole-support
length times the fundamental cycle of its whole second field pullback. -/
theorem fieldBaseChangeSupport_comp_fundamentalCycle :
    let := IntegralCycle.genericPointFintype (A.fieldBaseChangeSupport φ)
    let : ∀ z : genericPoints (A.fieldBaseChangeSupport φ),
        IsNoetherian (componentExterior (A.fieldBaseChangeSupportHom φ)
          (Spec.map (CommRingCat.ofHom ψ)) z) :=
      fun z => isNoetherian_of_finiteType
        (componentExteriorInclusion (A.fieldBaseChangeSupportHom φ)
          (Spec.map (CommRingCat.ofHom ψ)) z)
    fundamentalCycle (A.fieldBaseChangeSupport (ψ.comp φ)) =
      ∑ z : genericPoints (A.fieldBaseChangeSupport φ), (genericMultiplicity z : ℤ) •
        IntegralCycle.finitePushforward
          (componentExteriorInclusion (A.fieldBaseChangeSupportHom φ)
            (Spec.map (CommRingCat.ofHom ψ)) z ≫
              (A.fieldBaseChangeSupportTowerIso φ ψ).hom)
          (fundamentalCycle (componentExterior (A.fieldBaseChangeSupportHom φ)
            (Spec.map (CommRingCat.ofHom ψ)) z)) := by
  let : Flat (Spec.map (CommRingCat.ofHom ψ)) :=
    Flat.SpecMap_iff.mpr (RingHom.Flat.of_isField (Field.toIsField L) ψ)
  let := IntegralCycle.genericPointFintype (A.fieldBaseChangeSupport φ)
  let : ∀ z : genericPoints (A.fieldBaseChangeSupport φ),
      IsNoetherian (componentExterior (A.fieldBaseChangeSupportHom φ)
        (Spec.map (CommRingCat.ofHom ψ)) z) :=
    fun z => isNoetherian_of_finiteType
      (componentExteriorInclusion (A.fieldBaseChangeSupportHom φ)
        (Spec.map (CommRingCat.ofHom ψ)) z)
  rw [← A.finitePushforward_fieldBaseChangeSupportTower_fundamentalCycle φ ψ,
    fundamentalCycle_pullback_eq_component_sum (A.fieldBaseChangeSupportHom φ)
      (Spec.map (CommRingCat.ofHom ψ)), map_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [map_zsmul, IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply]

/-- The original composite-field correspondence cycle has the same weighted
tower decomposition in its faithful integral-cycle representation. -/
theorem toIntegralCycle_fieldBaseChangeCycle_comp :
    let := IntegralCycle.genericPointFintype (A.fieldBaseChangeSupport φ)
    let : ∀ z : genericPoints (A.fieldBaseChangeSupport φ),
        IsNoetherian (componentExterior (A.fieldBaseChangeSupportHom φ)
          (Spec.map (CommRingCat.ofHom ψ)) z) :=
      fun z => isNoetherian_of_finiteType
        (componentExteriorInclusion (A.fieldBaseChangeSupportHom φ)
          (Spec.map (CommRingCat.ofHom ψ)) z)
    FiniteCorrespondence.toIntegralCycle (A.fieldBaseChangeCycle (ψ.comp φ)) =
      ∑ z : genericPoints (A.fieldBaseChangeSupport φ), (genericMultiplicity z : ℤ) •
        IntegralCycle.finitePushforward
          (componentExteriorInclusion (A.fieldBaseChangeSupportHom φ)
            (Spec.map (CommRingCat.ofHom ψ)) z ≫
              (A.fieldBaseChangeSupportTowerIso φ ψ).hom ≫
                A.fieldBaseChangeInclusion (ψ.comp φ))
          (fundamentalCycle (componentExterior (A.fieldBaseChangeSupportHom φ)
            (Spec.map (CommRingCat.ofHom ψ)) z)) := by
  let := IntegralCycle.genericPointFintype (A.fieldBaseChangeSupport φ)
  let : ∀ z : genericPoints (A.fieldBaseChangeSupport φ),
      IsNoetherian (componentExterior (A.fieldBaseChangeSupportHom φ)
        (Spec.map (CommRingCat.ofHom ψ)) z) :=
    fun z => isNoetherian_of_finiteType
      (componentExteriorInclusion (A.fieldBaseChangeSupportHom φ)
        (Spec.map (CommRingCat.ofHom ψ)) z)
  rw [toIntegralCycle_fieldBaseChangeCycle,
    fieldBaseChangeSupport_comp_fundamentalCycle, map_sum]
  apply Finset.sum_congr rfl
  intro z _
  simp only [map_zsmul, IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply]

/-- The whole second pullback of an intermediate reduced component is
canonically the second support used by the actual field-change generator. -/
def fieldBaseChangeComponentSecondIso (z : genericPoints (A.fieldBaseChangeSupport φ)) :
    componentExterior (A.fieldBaseChangeSupportHom φ) (Spec.map (CommRingCat.ofHom ψ)) z ≅
      (A.fieldBaseChangeComponentGenerator φ z).fieldBaseChangeSupport ψ := by
  let f : componentExterior (A.fieldBaseChangeSupportHom φ)
      (Spec.map (CommRingCat.ofHom ψ)) z ⟶
        (A.fieldBaseChangeComponentGenerator φ z).fieldBaseChangeSupport ψ :=
    pullback.map _ _ _ _ (A.fieldBaseChangeComponentSchemeIso φ z).hom
      (𝟙 (Spec (.of M))) (𝟙 (Spec (.of L))) (by
        rw [Category.comp_id, ← Category.assoc,
          fieldBaseChangeComponentSchemeIso_hom_projection, Category.assoc]
        exact congrArg (fun f => (IntegralClosedSubscheme.pointClosure z.1).val.subschemeι ≫ f)
          (A.fieldBaseChangeProjection_snd φ).symm) (by simp)
  have : IsIso f := by
    dsimp only [f]
    exact pullback.map_isIso _ _ _ _ _ _ _ _ _
  exact asIso f

/-- This support comparison retains the original component's canonical image map. -/
@[reassoc (attr := simp)]
theorem fieldBaseChangeComponentSecondIso_hom_original
    (z : genericPoints (A.fieldBaseChangeSupport φ)) :
    (A.fieldBaseChangeComponentSecondIso φ ψ z).hom ≫
        (A.fieldBaseChangeComponentGenerator φ z).fieldBaseChangeSupportToOriginal ψ =
      pullback.fst ((IntegralClosedSubscheme.pointClosure z.1).val.subschemeι ≫
        A.fieldBaseChangeSupportHom φ) (Spec.map (CommRingCat.ofHom ψ)) ≫
          (A.fieldBaseChangeComponentSchemeIso φ z).hom := by
  simp only [fieldBaseChangeComponentSecondIso, asIso_hom, fieldBaseChangeSupportToOriginal,
    pullback.map, pullback.lift_fst]

/-- Its new field projection is unchanged, with no choice of a tensor branch. -/
@[reassoc (attr := simp)]
theorem fieldBaseChangeComponentSecondIso_hom_base
    (z : genericPoints (A.fieldBaseChangeSupport φ)) :
    (A.fieldBaseChangeComponentSecondIso φ ψ z).hom ≫
        (A.fieldBaseChangeComponentGenerator φ z).fieldBaseChangeSupportHom ψ =
      pullback.snd ((IntegralClosedSubscheme.pointClosure z.1).val.subschemeι ≫
        A.fieldBaseChangeSupportHom φ) (Spec.map (CommRingCat.ofHom ψ)) := by
  simp only [fieldBaseChangeComponentSecondIso, asIso_hom, fieldBaseChangeSupportHom,
    pullback.map, pullback.lift_snd, Category.comp_id]

/-- The original second field-change cycle of an intermediate component uses
its whole second pullback fundamental cycle under the canonical support map. -/
theorem toIntegralCycle_fieldBaseChangeComponentCycle
    (z : genericPoints (A.fieldBaseChangeSupport φ)) :
    let : IsNoetherian (componentExterior (A.fieldBaseChangeSupportHom φ)
        (Spec.map (CommRingCat.ofHom ψ)) z) :=
      isNoetherian_of_finiteType (A.fieldBaseChangeComponentSecondIso φ ψ z).hom
    FiniteCorrespondence.toIntegralCycle
      ((A.fieldBaseChangeComponentGenerator φ z).fieldBaseChangeCycle ψ) =
      IntegralCycle.finitePushforward
        ((A.fieldBaseChangeComponentSecondIso φ ψ z).hom ≫
          (A.fieldBaseChangeComponentGenerator φ z).fieldBaseChangeInclusion ψ)
        (fundamentalCycle (componentExterior (A.fieldBaseChangeSupportHom φ)
          (Spec.map (CommRingCat.ofHom ψ)) z)) := by
  let : IsNoetherian (componentExterior (A.fieldBaseChangeSupportHom φ)
      (Spec.map (CommRingCat.ofHom ψ)) z) :=
    isNoetherian_of_finiteType (A.fieldBaseChangeComponentSecondIso φ ψ z).hom
  simp only [toIntegralCycle_fieldBaseChangeCycle, IntegralCycle.finitePushforward_comp,
    AddMonoidHom.comp_apply, finitePushforward_fundamentalCycle]

/-- The original iterated signed-cycle map is the weighted sum over the same
whole second component pullbacks as the original composite-field map. The
ambient embeddings remain explicit and still need their tower comparison. -/
theorem toIntegralCycle_fieldBaseChangeCycle_iterated :
    let := IntegralCycle.genericPointFintype (A.fieldBaseChangeSupport φ)
    let : ∀ z : genericPoints (A.fieldBaseChangeSupport φ),
        IsNoetherian (componentExterior (A.fieldBaseChangeSupportHom φ)
          (Spec.map (CommRingCat.ofHom ψ)) z) :=
      fun z => isNoetherian_of_finiteType (A.fieldBaseChangeComponentSecondIso φ ψ z).hom
    FiniteCorrespondence.toIntegralCycle
      (FiniteCorrespondence.fieldBaseChange
        (X := (SmoothSite.fieldBaseChange φ).obj X)
        (Y := (SmoothSite.fieldBaseChange φ).obj Y) ψ (A.fieldBaseChangeCycle φ)) =
      ∑ z : genericPoints (A.fieldBaseChangeSupport φ), (genericMultiplicity z : ℤ) •
        IntegralCycle.finitePushforward
          ((A.fieldBaseChangeComponentSecondIso φ ψ z).hom ≫
            (A.fieldBaseChangeComponentGenerator φ z).fieldBaseChangeInclusion ψ)
          (fundamentalCycle (componentExterior (A.fieldBaseChangeSupportHom φ)
            (Spec.map (CommRingCat.ofHom ψ)) z)) := by
  let := IntegralCycle.genericPointFintype (A.fieldBaseChangeSupport φ)
  let : ∀ z : genericPoints (A.fieldBaseChangeSupport φ),
      IsNoetherian (componentExterior (A.fieldBaseChangeSupportHom φ)
        (Spec.map (CommRingCat.ofHom ψ)) z) :=
    fun z => isNoetherian_of_finiteType (A.fieldBaseChangeComponentSecondIso φ ψ z).hom
  rw [fieldBaseChangeCycle_eq_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [FiniteCorrespondence.fieldBaseChange_single, map_zsmul,
    toIntegralCycle_fieldBaseChangeComponentCycle]

end Motivic.FiniteCorrespondenceGenerator

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {k L M : Type u} [Field k] [Field L] [Field M]
  (φ : k →+* L) (ψ : L →+* M)

/-- The existing smooth-site tower comparison retains the two original
pullback projections on underlying schemes. -/
@[reassoc (attr := simp)]
theorem fieldBaseChangeComp_inv_original (X : overField k) :
    ((fieldBaseChangeComp φ ψ).inv.app X).left ≫
        pullback.fst X.hom (Spec.map (CommRingCat.ofHom φ ≫ CommRingCat.ofHom ψ)) =
      pullback.fst ((fieldBaseChange φ).obj X).hom (Spec.map (CommRingCat.ofHom ψ)) ≫
        pullback.fst X.hom (Spec.map (CommRingCat.ofHom φ)) := by
  simp [fieldBaseChangeComp]

/-- Its scalar projection is the actual final pullback projection. -/
@[reassoc (attr := simp)]
theorem fieldBaseChangeComp_inv_base (X : overField k) :
    ((fieldBaseChangeComp φ ψ).inv.app X).left ≫
        pullback.snd X.hom (Spec.map (CommRingCat.ofHom φ ≫ CommRingCat.ofHom ψ)) =
      pullback.snd ((fieldBaseChange φ).obj X).hom (Spec.map (CommRingCat.ofHom ψ)) :=
  MorphismProperty.Over.w _

/-- The canonical product comparison between the iterated and direct
field-change ambient schemes, using the existing smooth-site comparisons. -/
def fieldBaseChangeProductTowerIso (X Y : overField k) :
    (product ((fieldBaseChange ψ).obj ((fieldBaseChange φ).obj X))
      ((fieldBaseChange ψ).obj ((fieldBaseChange φ).obj Y))).left ≅
    (product ((fieldBaseChange (ψ.comp φ)).obj X)
      ((fieldBaseChange (ψ.comp φ)).obj Y)).left :=
  (forgetScheme (Spec (.of M))).mapIso
    (productIso ((fieldBaseChangeComp φ ψ).app X).symm
      ((fieldBaseChangeComp φ ψ).app Y).symm)

@[reassoc (attr := simp)]
theorem fieldBaseChangeProductTowerIso_hom_fst (X Y : overField k) :
    (fieldBaseChangeProductTowerIso φ ψ X Y).hom ≫
      pullback.fst
        (pullback.snd X.hom (Spec.map (CommRingCat.ofHom φ ≫ CommRingCat.ofHom ψ)))
        (pullback.snd Y.hom (Spec.map (CommRingCat.ofHom φ ≫ CommRingCat.ofHom ψ))) =
    pullback.fst ((fieldBaseChange ψ).obj ((fieldBaseChange φ).obj X)).hom
        ((fieldBaseChange ψ).obj ((fieldBaseChange φ).obj Y)).hom ≫
      ((fieldBaseChangeComp φ ψ).inv.app X).left :=
  congrArg (fun f => f.left)
    (productMap_fst ((fieldBaseChangeComp φ ψ).inv.app X)
      ((fieldBaseChangeComp φ ψ).inv.app Y))

@[reassoc (attr := simp)]
theorem fieldBaseChangeProductTowerIso_hom_snd (X Y : overField k) :
    (fieldBaseChangeProductTowerIso φ ψ X Y).hom ≫
      pullback.snd
        (pullback.snd X.hom (Spec.map (CommRingCat.ofHom φ ≫ CommRingCat.ofHom ψ)))
        (pullback.snd Y.hom (Spec.map (CommRingCat.ofHom φ ≫ CommRingCat.ofHom ψ))) =
    pullback.snd ((fieldBaseChange ψ).obj ((fieldBaseChange φ).obj X)).hom
        ((fieldBaseChange ψ).obj ((fieldBaseChange φ).obj Y)).hom ≫
      ((fieldBaseChangeComp φ ψ).inv.app Y).left :=
  congrArg (fun f => f.left)
    (productMap_snd ((fieldBaseChangeComp φ ψ).inv.app X)
      ((fieldBaseChangeComp φ ψ).inv.app Y))

end AlgebraicGeometry.Scheme.SmoothSite

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme

variable {k L M : Type u} [Field k] [Field L] [Field M]
  (φ : k →+* L) (ψ : L →+* M)
  {X Y : SmoothSite.overField k} (A : FiniteCorrespondenceGenerator X.hom Y.hom)

/-- Each actual second component inclusion commutes with the canonical ambient
tower isomorphism and the original composite-field support inclusion. -/
@[reassoc]
theorem fieldBaseChangeComponentSecondIso_hom_ambient
    (z : genericPoints (A.fieldBaseChangeSupport φ)) :
    (A.fieldBaseChangeComponentSecondIso φ ψ z).hom ≫
        (A.fieldBaseChangeComponentGenerator φ z).fieldBaseChangeInclusion ψ ≫
          (SmoothSite.fieldBaseChangeProductTowerIso φ ψ X Y).hom =
      componentExteriorInclusion (A.fieldBaseChangeSupportHom φ)
        (Spec.map (CommRingCat.ofHom ψ)) z ≫
          (A.fieldBaseChangeSupportTowerIso φ ψ).hom ≫
            A.fieldBaseChangeInclusion (ψ.comp φ) := by
  apply pullback.hom_ext
  · simp only [Category.assoc]
    erw [SmoothSite.fieldBaseChangeProductTowerIso_hom_fst φ ψ X Y]
    simp only [fieldBaseChangeInclusion_fst,
      fieldBaseChangeInclusion_fst_assoc]
    apply pullback.hom_ext
    · simp only [Category.assoc]
      erw [SmoothSite.fieldBaseChangeComp_inv_original φ ψ X]
      simp only [fieldBaseChangeProjection_fst_assoc,
        fieldBaseChangeProjection_fst,
        fieldBaseChangeComponentSecondIso_hom_original_assoc,
        fieldBaseChangeComponentSchemeIso_hom_projection_assoc,
        fieldBaseChangeSupportTowerIso_hom_original_assoc,
        IntegralClosedSubscheme.exteriorInclusion_fst_assoc]
    · simp only [Category.assoc]
      erw [SmoothSite.fieldBaseChangeComp_inv_base φ ψ X]
      simp only [fieldBaseChangeProjection_snd,
        fieldBaseChangeComponentSecondIso_hom_base,
        fieldBaseChangeSupportTowerIso_hom_base,
        IntegralClosedSubscheme.exteriorInclusion_snd]
  · simp only [Category.assoc]
    erw [SmoothSite.fieldBaseChangeProductTowerIso_hom_snd φ ψ X Y]
    simp only [fieldBaseChangeInclusion_snd,
      fieldBaseChangeInclusion_snd_assoc]
    apply pullback.hom_ext
    · simp only [Category.assoc]
      erw [SmoothSite.fieldBaseChangeComp_inv_original φ ψ Y]
      simp only [fieldBaseChangeTargetProjection_fst_assoc,
        fieldBaseChangeTargetProjection_fst,
        fieldBaseChangeComponentSecondIso_hom_original_assoc,
        fieldBaseChangeComponentSchemeIso_hom_targetProjection_assoc,
        fieldBaseChangeSupportTowerIso_hom_original_assoc,
        IntegralClosedSubscheme.exteriorInclusion_fst_assoc]
    · have h₁ : (A.fieldBaseChangeComponentGenerator φ z).fieldBaseChangeTargetProjection ψ ≫
          pullback.snd ((SmoothSite.fieldBaseChange φ).obj Y).hom
            (Spec.map (CommRingCat.ofHom ψ)) =
          (A.fieldBaseChangeComponentGenerator φ z).fieldBaseChangeSupportHom ψ :=
        (A.fieldBaseChangeComponentGenerator φ z).fieldBaseChangeTargetProjection_snd ψ
      have h₂ : A.fieldBaseChangeTargetProjection (ψ.comp φ) ≫
          pullback.snd Y.hom (Spec.map (CommRingCat.ofHom (ψ.comp φ))) =
          A.fieldBaseChangeSupportHom (ψ.comp φ) :=
        A.fieldBaseChangeTargetProjection_snd (ψ.comp φ)
      simp only [Category.assoc]
      erw [SmoothSite.fieldBaseChangeComp_inv_base φ ψ Y]
      simp only [h₁, h₂,
        fieldBaseChangeComponentSecondIso_hom_base, fieldBaseChangeSupportTowerIso_hom_base,
        IntegralClosedSubscheme.exteriorInclusion_snd]

/-- The actual twice-changed generator cycle equals the original
composite-field cycle under the canonical ambient product comparison. -/
theorem toIntegralCycle_fieldBaseChange_comp_cycle :
    IntegralCycle.finitePushforward (SmoothSite.fieldBaseChangeProductTowerIso φ ψ X Y).hom
      (FiniteCorrespondence.toIntegralCycle
        (FiniteCorrespondence.fieldBaseChange
          (X := (SmoothSite.fieldBaseChange φ).obj X)
          (Y := (SmoothSite.fieldBaseChange φ).obj Y) ψ (A.fieldBaseChangeCycle φ))) =
      FiniteCorrespondence.toIntegralCycle (A.fieldBaseChangeCycle (ψ.comp φ)) := by
  let := IntegralCycle.genericPointFintype (A.fieldBaseChangeSupport φ)
  let : ∀ z : genericPoints (A.fieldBaseChangeSupport φ),
      IsNoetherian (componentExterior (A.fieldBaseChangeSupportHom φ)
        (Spec.map (CommRingCat.ofHom ψ)) z) :=
    fun z => isNoetherian_of_finiteType (A.fieldBaseChangeComponentSecondIso φ ψ z).hom
  rw [toIntegralCycle_fieldBaseChangeCycle_iterated, map_sum,
    toIntegralCycle_fieldBaseChangeCycle_comp]
  apply Finset.sum_congr rfl
  intro z _
  rw [map_zsmul]
  apply congrArg (fun c => (genericMultiplicity z : ℤ) • c)
  rw [← AddMonoidHom.comp_apply, ← IntegralCycle.finitePushforward_comp]
  congr 2
  exact (Category.assoc _ _ _).trans (A.fieldBaseChangeComponentSecondIso_hom_ambient φ ψ z)

end Motivic.FiniteCorrespondenceGenerator

namespace Motivic.FiniteCorrespondence
open _root_.AlgebraicGeometry.Scheme

variable {k L M : Type u} [Field k] [Field L] [Field M]
  (φ : k →+* L) (ψ : L →+* M) {X Y : SmoothSite.overField k}

/-- The original iterated field-change map on every signed correspondence is
exactly the original composite-field map under the canonical product isomorphism.
This compares the actual weighted cycles, not only their reduced supports. -/
theorem toIntegralCycle_fieldBaseChange_comp (α : FiniteCorrespondence X.hom Y.hom) :
    IntegralCycle.finitePushforward (SmoothSite.fieldBaseChangeProductTowerIso φ ψ X Y).hom
      (toIntegralCycle (fieldBaseChange
        (X := (SmoothSite.fieldBaseChange φ).obj X)
        (Y := (SmoothSite.fieldBaseChange φ).obj Y) ψ
        (fieldBaseChange (X := X) (Y := Y) φ α))) =
      toIntegralCycle (fieldBaseChange (X := X) (Y := Y) (ψ.comp φ) α) := by
  have h :
      (IntegralCycle.finitePushforward
        (SmoothSite.fieldBaseChangeProductTowerIso φ ψ X Y).hom).comp
        (toIntegralCycle.comp
          ((fieldBaseChange (X := (SmoothSite.fieldBaseChange φ).obj X)
            (Y := (SmoothSite.fieldBaseChange φ).obj Y) ψ).comp
              (fieldBaseChange (X := X) (Y := Y) φ))) =
      toIntegralCycle.comp (fieldBaseChange (X := X) (Y := Y) (ψ.comp φ)) := by
    apply Finsupp.addHom_ext
    intro A n
    change IntegralCycle.finitePushforward
        (SmoothSite.fieldBaseChangeProductTowerIso φ ψ X Y).hom
        (toIntegralCycle (fieldBaseChange
          (X := (SmoothSite.fieldBaseChange φ).obj X)
          (Y := (SmoothSite.fieldBaseChange φ).obj Y) ψ
          (fieldBaseChange (X := X) (Y := Y) φ (Finsupp.single A n)))) =
        toIntegralCycle (fieldBaseChange (X := X) (Y := Y) (ψ.comp φ) (Finsupp.single A n))
    simpa only [fieldBaseChange_single, map_zsmul] using
      congrArg (fun c => n • c) (A.toIntegralCycle_fieldBaseChange_comp_cycle φ ψ)
  exact DFunLike.congr_fun h α

end Motivic.FiniteCorrespondence

namespace AlgebraicGeometry.Scheme.SmoothSite

variable (k : Type u) [Field k]

/-- The literal first projection of identity-field base change is invertible. -/
theorem fieldBaseChangeIdProjection_isIso (X : overField k) :
    IsIso (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (RingHom.id k)))) := by
  rw [CommRingCat.ofHom_id, Spec.map_id]
  infer_instance

/-- The canonical identity-field object comparison, constructed directly from
its actual pullback projection without unfolding a functor transport. -/
def fieldBaseChangeObjectIdIso (X : overField k) :
    (fieldBaseChange (RingHom.id k)).obj X ≅ X := by
  let : IsIso (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (RingHom.id k)))) :=
    fieldBaseChangeIdProjection_isIso k X
  refine MorphismProperty.Over.isoMk
    (asIso (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (RingHom.id k))))) ?_
  change pullback.fst X.hom (Spec.map (CommRingCat.ofHom (RingHom.id k))) ≫ X.hom =
    pullback.snd X.hom (Spec.map (CommRingCat.ofHom (RingHom.id k)))
  exact pullback.condition.trans (by rw [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id])

/-- The canonical identity object comparison retains the literal projection. -/
@[simp]
theorem fieldBaseChangeObjectIdIso_hom_left (X : overField k) :
    (fieldBaseChangeObjectIdIso k X).hom.left =
      pullback.fst X.hom (Spec.map (CommRingCat.ofHom (RingHom.id k))) := rfl

/-- The original product ambient scheme is recovered by the canonical
identity projections on its two factors. -/
def fieldBaseChangeProductIdIso (X Y : overField k) :
    (product ((fieldBaseChange (RingHom.id k)).obj X)
      ((fieldBaseChange (RingHom.id k)).obj Y)).left ≅ (product X Y).left :=
  (forgetScheme (Spec (.of k))).mapIso
    (productIso (fieldBaseChangeObjectIdIso k X) (fieldBaseChangeObjectIdIso k Y))

@[reassoc (attr := simp)]
theorem fieldBaseChangeProductIdIso_hom_fst (X Y : overField k) :
    (fieldBaseChangeProductIdIso k X Y).hom ≫ pullback.fst X.hom Y.hom =
      pullback.fst ((fieldBaseChange (RingHom.id k)).obj X).hom
          ((fieldBaseChange (RingHom.id k)).obj Y).hom ≫
        (fieldBaseChangeObjectIdIso k X).hom.left :=
  congrArg (fun f => f.left)
    (productMap_fst (fieldBaseChangeObjectIdIso k X).hom (fieldBaseChangeObjectIdIso k Y).hom)

@[reassoc (attr := simp)]
theorem fieldBaseChangeProductIdIso_hom_snd (X Y : overField k) :
    (fieldBaseChangeProductIdIso k X Y).hom ≫ pullback.snd X.hom Y.hom =
      pullback.snd ((fieldBaseChange (RingHom.id k)).obj X).hom
          ((fieldBaseChange (RingHom.id k)).obj Y).hom ≫
        (fieldBaseChangeObjectIdIso k Y).hom.left :=
  congrArg (fun f => f.left)
    (productMap_snd (fieldBaseChangeObjectIdIso k X).hom (fieldBaseChangeObjectIdIso k Y).hom)

end AlgebraicGeometry.Scheme.SmoothSite

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X Y : SmoothSite.overField k}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)

/-- The original identity-field support inclusion commutes with the canonical
identity comparison of the actual ambient product. -/
@[reassoc]
theorem fieldBaseChangeSupportIdIso_hom_ambient :
    A.fieldBaseChangeInclusion (RingHom.id k) ≫
        (SmoothSite.fieldBaseChangeProductIdIso k X Y).hom =
      A.fieldBaseChangeSupportIdIso.hom ≫ A.inclusion := by
  apply pullback.hom_ext
  · simp only [Category.assoc, SmoothSite.fieldBaseChangeProductIdIso_hom_fst,
      fieldBaseChangeInclusion_fst_assoc, SmoothSite.fieldBaseChangeObjectIdIso_hom_left,
      fieldBaseChangeProjection_fst, fieldBaseChangeSupportIdIso_hom]
    rfl
  · simp only [Category.assoc, SmoothSite.fieldBaseChangeProductIdIso_hom_snd,
      fieldBaseChangeInclusion_snd_assoc, SmoothSite.fieldBaseChangeObjectIdIso_hom_left,
      fieldBaseChangeTargetProjection_fst, fieldBaseChangeSupportIdIso_hom]

end Motivic.FiniteCorrespondenceGenerator

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X Y : SmoothSite.overField k}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)

/-- The original identity-field generator cycle becomes the original generator
cycle under the canonical ambient identity comparison. -/
theorem toIntegralCycle_fieldBaseChange_id_cycle :
    IntegralCycle.finitePushforward (SmoothSite.fieldBaseChangeProductIdIso k X Y).hom
      (FiniteCorrespondence.toIntegralCycle (A.fieldBaseChangeCycle (RingHom.id k))) =
        FiniteCorrespondence.toIntegralCycle A.cycle := by
  let : IsNoetherian ((𝟭 Scheme).obj X.left) := inferInstanceAs (IsNoetherian X.left)
  let : IsNoetherian A.scheme := isNoetherian_of_finiteType A.projection
  rw [toIntegralCycle_fieldBaseChangeCycle, ← AddMonoidHom.comp_apply,
    ← IntegralCycle.finitePushforward_comp,
    IntegralCycle.finitePushforward_congr A.fieldBaseChangeSupportIdIso_hom_ambient,
    IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply,
    finitePushforward_fieldBaseChangeSupportId_fundamentalCycle]
  let : IsNoetherian (pullback X.hom Y.hom) :=
    isNoetherian_of_finiteType (pullback.fst X.hom Y.hom)
  change closedFundamentalCycle A.val = FiniteCorrespondence.toIntegralCycle A.cycle
  rw [closedFundamentalCycle_of_isIntegral, cycle, FiniteCorrespondence.toIntegralCycle_single]
  rfl

end Motivic.FiniteCorrespondenceGenerator

namespace Motivic.FiniteCorrespondence
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X Y : SmoothSite.overField k}

/-- The original identity-field map on every signed correspondence is the
original cycle under the canonical product identity comparison. -/
theorem toIntegralCycle_fieldBaseChange_id (α : FiniteCorrespondence X.hom Y.hom) :
    IntegralCycle.finitePushforward (SmoothSite.fieldBaseChangeProductIdIso k X Y).hom
      (toIntegralCycle (fieldBaseChange (X := X) (Y := Y) (RingHom.id k) α)) =
        toIntegralCycle α := by
  have h :
      (IntegralCycle.finitePushforward (SmoothSite.fieldBaseChangeProductIdIso k X Y).hom).comp
        (toIntegralCycle.comp (fieldBaseChange (X := X) (Y := Y) (RingHom.id k))) =
      toIntegralCycle := by
    apply Finsupp.addHom_ext
    intro A n
    change IntegralCycle.finitePushforward (SmoothSite.fieldBaseChangeProductIdIso k X Y).hom
        (toIntegralCycle (fieldBaseChange (X := X) (Y := Y) (RingHom.id k)
          (Finsupp.single A n))) = toIntegralCycle (Finsupp.single A n)
    have hs : Finsupp.single A n = n • A.cycle := by
      simp [FiniteCorrespondenceGenerator.cycle]
    rw [hs]
    simpa only [map_zsmul, fieldBaseChange_cycle] using
      congrArg (fun c => n • c) A.toIntegralCycle_fieldBaseChange_id_cycle
  exact DFunLike.congr_fun h α

end Motivic.FiniteCorrespondence
