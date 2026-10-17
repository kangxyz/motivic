/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.SmoothSiteBaseChangeProducts
public import Motivic.Aglib.AlgebraicGeometry.FlatBaseChangeGeneric
public import Motivic.AlgebraicGeometry.SmoothSiteNormal
public import Motivic.AlgebraicGeometry.Cycles.CorrespondenceCycle
public import Motivic.AlgebraicGeometry.Cycles.FundamentalCycle
public import Motivic.AlgebraicGeometry.Cycles.FiniteImageProjection

/-!
# Actual finite-correspondence supports under arbitrary field change

The support is the whole scheme-theoretic fiber product with the new field.
Its projection is the actual finite base change of the original projection.
No finite-type assumption on the field extension and no reducedness assumption
on the pulled-back support is made. Generic local lengths remain the
fundamental multiplicities; this file does not assert compatibility with the
weighted Tor composition of correspondences.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondenceGenerator

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L)
  {X Y : SmoothSite.overField k} (A : FiniteCorrespondenceGenerator X.hom Y.hom)

/-- The literal whole support `A ×_k Spec L`, before taking reduced components. -/
abbrev fieldBaseChangeSupport : Scheme.{u} :=
  pullback (A.projection ≫ X.hom) (Spec.map (CommRingCat.ofHom φ))

/-- Projection from the whole support onto the actual new smooth source. -/
def fieldBaseChangeProjection : A.fieldBaseChangeSupport φ ⟶
    ((SmoothSite.fieldBaseChange φ).obj X).left :=
  pullback.lift
    (pullback.fst (A.projection ≫ X.hom) (Spec.map (CommRingCat.ofHom φ)) ≫ A.projection)
    (pullback.snd (A.projection ≫ X.hom) (Spec.map (CommRingCat.ofHom φ)))
    (by simpa only [Category.assoc] using (pullback.condition
      (f := A.projection ≫ X.hom) (g := Spec.map (CommRingCat.ofHom φ))))

@[reassoc (attr := simp)]
theorem fieldBaseChangeProjection_fst :
    A.fieldBaseChangeProjection φ ≫ pullback.fst X.hom (Spec.map (CommRingCat.ofHom φ)) =
      pullback.fst (A.projection ≫ X.hom) (Spec.map (CommRingCat.ofHom φ)) ≫ A.projection :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem fieldBaseChangeProjection_snd :
    A.fieldBaseChangeProjection φ ≫ pullback.snd X.hom (Spec.map (CommRingCat.ofHom φ)) =
      pullback.snd (A.projection ≫ X.hom) (Spec.map (CommRingCat.ofHom φ)) :=
  pullback.lift_snd _ _ _

/-- The source projection square is Cartesian with its original maps unchanged. -/
theorem fieldBaseChangeProjection_isPullback :
    IsPullback
      (pullback.fst (A.projection ≫ X.hom) (Spec.map (CommRingCat.ofHom φ)))
      (A.fieldBaseChangeProjection φ) A.projection
      (pullback.fst X.hom (Spec.map (CommRingCat.ofHom φ))) := by
  refine IsPullback.of_bot (t := IsPullback.of_hasPullback X.hom
    (Spec.map (CommRingCat.ofHom φ))) ?_ (A.fieldBaseChangeProjection_fst φ).symm
  simpa only [A.fieldBaseChangeProjection_snd φ] using
    IsPullback.of_hasPullback (A.projection ≫ X.hom) (Spec.map (CommRingCat.ofHom φ))

/-- Finiteness is inherited from the original finite correspondence. -/
instance fieldBaseChangeProjection_isFinite : IsFinite (A.fieldBaseChangeProjection φ) :=
  MorphismProperty.of_isPullback (A.fieldBaseChangeProjection_isPullback φ) inferInstance

/-- Closed inclusion into the base change of the old product ambient scheme. -/
def fieldBaseChangeAmbientInclusion : A.fieldBaseChangeSupport φ ⟶
    ((SmoothSite.fieldBaseChange φ).obj (SmoothSite.product X Y)).left :=
  pullback.lift
    (pullback.fst (A.projection ≫ X.hom) (Spec.map (CommRingCat.ofHom φ)) ≫ A.inclusion)
    (pullback.snd (A.projection ≫ X.hom) (Spec.map (CommRingCat.ofHom φ))) (by
      simpa only [SmoothSite.product_hom, projection, correspondenceProjection, inclusion,
        Category.assoc] using (pullback.condition (f := A.projection ≫ X.hom)
          (g := Spec.map (CommRingCat.ofHom φ))))

@[reassoc (attr := simp)]
theorem fieldBaseChangeAmbientInclusion_fst :
    A.fieldBaseChangeAmbientInclusion φ ≫
      pullback.fst (SmoothSite.product X Y).hom (Spec.map (CommRingCat.ofHom φ)) =
        pullback.fst (A.projection ≫ X.hom) (Spec.map (CommRingCat.ofHom φ)) ≫ A.inclusion :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem fieldBaseChangeAmbientInclusion_snd :
    A.fieldBaseChangeAmbientInclusion φ ≫
      pullback.snd (SmoothSite.product X Y).hom (Spec.map (CommRingCat.ofHom φ)) =
        pullback.snd (A.projection ≫ X.hom) (Spec.map (CommRingCat.ofHom φ)) :=
  pullback.lift_snd _ _ _

/-- The full support immersion is pulled back, without replacing its ideal by its radical. -/
theorem fieldBaseChangeAmbientInclusion_isPullback :
    IsPullback
      (pullback.fst (A.projection ≫ X.hom) (Spec.map (CommRingCat.ofHom φ)))
      (A.fieldBaseChangeAmbientInclusion φ) A.inclusion
      (pullback.fst (SmoothSite.product X Y).hom (Spec.map (CommRingCat.ofHom φ))) := by
  refine IsPullback.of_bot (t := IsPullback.of_hasPullback (SmoothSite.product X Y).hom
    (Spec.map (CommRingCat.ofHom φ))) ?_ (A.fieldBaseChangeAmbientInclusion_fst φ).symm
  rw [A.fieldBaseChangeAmbientInclusion_snd φ]
  simpa only [SmoothSite.product_hom,
    projection, correspondenceProjection, inclusion, Category.assoc] using
      IsPullback.of_hasPullback (A.projection ≫ X.hom) (Spec.map (CommRingCat.ofHom φ))

instance fieldBaseChangeAmbientInclusion_isClosedImmersion :
    IsClosedImmersion (A.fieldBaseChangeAmbientInclusion φ) :=
  MorphismProperty.of_isPullback (A.fieldBaseChangeAmbientInclusion_isPullback φ) inferInstance

/-- The actual support embedded in the product over the new field. -/
def fieldBaseChangeInclusion : A.fieldBaseChangeSupport φ ⟶
    (SmoothSite.product ((SmoothSite.fieldBaseChange φ).obj X)
      ((SmoothSite.fieldBaseChange φ).obj Y)).left :=
  A.fieldBaseChangeAmbientInclusion φ ≫
    (SmoothSite.baseChangeProductIso (Spec.map (CommRingCat.ofHom φ)) X Y).hom.left

instance fieldBaseChangeInclusion_isClosedImmersion :
    IsClosedImmersion (A.fieldBaseChangeInclusion φ) := by
  unfold fieldBaseChangeInclusion
  infer_instance

/-- The new ambient inclusion has exactly the original base-changed source projection. -/
@[reassoc (attr := simp)]
theorem fieldBaseChangeInclusion_fst :
    A.fieldBaseChangeInclusion φ ≫
      pullback.fst ((SmoothSite.fieldBaseChange φ).obj X).hom
        ((SmoothSite.fieldBaseChange φ).obj Y).hom = A.fieldBaseChangeProjection φ := by
  unfold fieldBaseChangeInclusion
  have h := congrArg (fun e => e.left)
    (SmoothSite.baseChangeProductIso_hom_fst (Spec.map (CommRingCat.ofHom φ)) X Y)
  dsimp only [MorphismProperty.Comma.comp_left, SmoothSite.productFst,
    SmoothSite.homMk_left] at h
  dsimp only [SmoothSite.fieldBaseChange]
  rw [Category.assoc, h]
  apply pullback.hom_ext
  · rw [Category.assoc, SmoothSite.baseChange_map_fst,
      fieldBaseChangeProjection_fst, ← Category.assoc,
      fieldBaseChangeAmbientInclusion_fst]
    rfl
  · simp only [Category.assoc, SmoothSite.baseChange_map_snd,
      fieldBaseChangeAmbientInclusion_snd, fieldBaseChangeProjection_snd]

/-- Noetherianity comes from the new smooth source, not from finite type of `L/k`. -/
instance fieldBaseChangeSupport_isNoetherian : IsNoetherian (A.fieldBaseChangeSupport φ) :=
  isNoetherian_of_finiteType (A.fieldBaseChangeProjection φ)

/-- Every reduced integral component still has finite projection. -/
instance fieldBaseChangeComponent_isFinite (w : genericPoints (A.fieldBaseChangeSupport φ)) :
    IsFinite ((IntegralClosedSubscheme.pointClosure w.1).val.subschemeι ≫
      A.fieldBaseChangeProjection φ) := inferInstance

/-- The finite component projection has exactly the closure of the mapped generic point
as its image, without any assumption that the whole support is reduced. -/
theorem fieldBaseChangeComponent_range
    (w : genericPoints (A.fieldBaseChangeSupport φ)) :
    Set.range ((IntegralClosedSubscheme.pointClosure w.1).val.subschemeι ≫
      A.fieldBaseChangeProjection φ) =
        closure ({A.fieldBaseChangeProjection φ w.1} :
          Set ((SmoothSite.fieldBaseChange φ).obj X).left) := by
  change Set.range ((A.fieldBaseChangeProjection φ) ∘
    (IntegralClosedSubscheme.pointClosure w.1).val.subschemeι) = _
  rw [Set.range_comp, (IntegralClosedSubscheme.pointClosure w.1).val.range_subschemeι,
    IntegralClosedSubscheme.support_pointClosure,
    ← (A.fieldBaseChangeProjection φ).isClosedMap.closure_image_eq_of_continuous
      (A.fieldBaseChangeProjection φ).continuous, Set.image_singleton]

/-- Every component generic of the actual pulled-back support dominates a component
of the new smooth source, even for arbitrary and inseparable field extensions. -/
theorem fieldBaseChangeProjection_generic
    (w : genericPoints (A.fieldBaseChangeSupport φ)) :
    A.fieldBaseChangeProjection φ w.1 ∈
      genericPoints ((SmoothSite.fieldBaseChange φ).obj X).left := by
  have : Flat (Spec.map (CommRingCat.ofHom φ)) :=
    Flat.SpecMap_iff.mpr (RingHom.Flat.of_isField (Field.toIsField k) φ)
  have : IsNoetherian ((𝟭 Scheme).obj X.left) :=
    inferInstanceAs (IsNoetherian X.left)
  exact mem_genericPoints_of_isPullback_flat_component
    (A.fieldBaseChangeProjection φ) _ _ A.projection
    (A.fieldBaseChangeProjection_isPullback φ).flip A.range_projection_mem
    (fun x => SmoothSite.isDomain_stalk L _ x)
    (fun x => SmoothSite.isDomain_stalk k X x) w.1 w.2

/-- Each reduced integral component is finite and surjective onto an actual
irreducible component of the new smooth source. -/
theorem fieldBaseChangeComponent_range_mem
    (w : genericPoints (A.fieldBaseChangeSupport φ)) :
    Set.range ((IntegralClosedSubscheme.pointClosure w.1).val.subschemeι ≫
      A.fieldBaseChangeProjection φ) ∈
        irreducibleComponents ((SmoothSite.fieldBaseChange φ).obj X).left := by
  rw [A.fieldBaseChangeComponent_range φ w]
  exact A.fieldBaseChangeProjection_generic φ w

/-- The image of each reduced integral support component in the new product is
an admissible finite-correspondence generator. No multiplicity is assigned here. -/
def fieldBaseChangeComponentGenerator
    (w : genericPoints (A.fieldBaseChangeSupport φ)) :
    FiniteCorrespondenceGenerator ((SmoothSite.fieldBaseChange φ).obj X).hom
      ((SmoothSite.fieldBaseChange φ).obj Y).hom := by
  let C := IntegralClosedSubscheme.pointClosure w.1
  refine ⟨(C.finiteImage (A.fieldBaseChangeInclusion φ)).val,
    (C.finiteImage (A.fieldBaseChangeInclusion φ)).property, ?_, ?_⟩
  · have : IsFinite ((C.val.subschemeι ≫ A.fieldBaseChangeInclusion φ) ≫
        pullback.fst ((SmoothSite.fieldBaseChange φ).obj X).hom
          ((SmoothSite.fieldBaseChange φ).obj Y).hom) := by
      simpa only [Category.assoc, fieldBaseChangeInclusion_fst] using
        (inferInstance : IsFinite (C.val.subschemeι ≫ A.fieldBaseChangeProjection φ))
    exact isFinite_image_projection (C.val.subschemeι ≫ A.fieldBaseChangeInclusion φ) _
  · change Set.range ((C.val.subschemeι ≫ A.fieldBaseChangeInclusion φ).imageι ≫
      pullback.fst ((SmoothSite.fieldBaseChange φ).obj X).hom
        ((SmoothSite.fieldBaseChange φ).obj Y).hom) ∈ _
    rw [range_image_projection, Category.assoc, fieldBaseChangeInclusion_fst]
    exact A.fieldBaseChangeComponent_range_mem φ w

/-- The new generator uses the actual closed image of the reduced component. -/
@[simp]
theorem fieldBaseChangeComponentGenerator_val
    (w : genericPoints (A.fieldBaseChangeSupport φ)) :
    (A.fieldBaseChangeComponentGenerator φ w).val =
      ((IntegralClosedSubscheme.pointClosure w.1).finiteImage
        (A.fieldBaseChangeInclusion φ)).val := rfl

/-- The whole support's actual fundamental cycle retains all generic lengths. -/
def fieldBaseChangeSupportCycle : IntegralCycle (A.fieldBaseChangeSupport φ) :=
  fundamentalCycle (A.fieldBaseChangeSupport φ)

/-- Coefficients are lengths in the whole support, never in its reduced component. -/
theorem fieldBaseChangeSupportCycle_component
    (w : genericPoints (A.fieldBaseChangeSupport φ)) :
    A.fieldBaseChangeSupportCycle φ (IntegralClosedSubscheme.pointClosure w.1) =
      (genericMultiplicity w : ℤ) :=
  fundamentalCycle_component w

end Motivic.FiniteCorrespondenceGenerator
