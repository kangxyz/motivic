/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.BaseChange.Field.Cycle
public import Motivic.AlgebraicGeometry.Correspondences.Exterior.Simplex.Graph
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.QuasiFinite.GenericFiber

/-!
# Actual whole graph cycles under arbitrary field change

The base change of each original graph component has open source projection,
so its entire support is reduced. Its possibly several generic points are
partitioned by the original source components. This gives the whole graph
cycle over the new field, including disconnected and empty smooth sources.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

universe u

namespace Motivic
open _root_.AlgebraicGeometry.Scheme

local instance fieldBaseChangeGraph_isNoetherian_idObj
    {k : Type u} [Field k] (X : SmoothSite.overField k) :
    IsNoetherian ((𝟭 Scheme).obj X.left) := inferInstanceAs (IsNoetherian X.left)

local instance fieldBaseChangeGraph_isReduced_idObj
    {k : Type u} [Field k] (X : SmoothSite.overField k) :
    IsReduced ((𝟭 Scheme).obj X.left) := inferInstanceAs (IsReduced X.left)

namespace FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Hom

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L)
  {X Y : SmoothSite.overField k} (A : FiniteCorrespondenceGenerator X.hom Y.hom)

/-- The Cartesian support projection has the literal preimage of the original range. -/
theorem fieldBaseChangeProjection_range :
    Set.range (A.fieldBaseChangeProjection φ) =
      (pullback.fst X.hom (Spec.map (CommRingCat.ofHom φ))) ⁻¹' Set.range A.projection := by
  let h := (A.fieldBaseChangeProjection_isPullback φ).flip
  rw [← h.isoPullback_hom_fst]
  change Set.range (fun x =>
    (pullback.fst (pullback.fst X.hom (Spec.map (CommRingCat.ofHom φ))) A.projection)
      (h.isoPullback.hom x)) = _
  exact ((Scheme.homeoOfIso h.isoPullback).surjective.range_comp _).trans
    (Scheme.Pullback.range_fst _ _)

/-- The actual new support still satisfies the graph relation. -/
theorem fieldBaseChangeInclusion_graph (f : X ⟶ Y)
    (hA : A.projection ≫ f.left = A.targetProjection) :
    A.fieldBaseChangeProjection φ ≫ ((SmoothSite.fieldBaseChange φ).map f).left =
      A.fieldBaseChangeInclusion φ ≫
        pullback.snd ((SmoothSite.fieldBaseChange φ).obj X).hom
          ((SmoothSite.fieldBaseChange φ).obj Y).hom := by
  unfold fieldBaseChangeInclusion
  have h := congrArg (fun e => e.left)
    (SmoothSite.baseChangeProductIso_hom_snd (Spec.map (CommRingCat.ofHom φ)) X Y)
  dsimp only [MorphismProperty.Comma.comp_left, SmoothSite.productSnd,
    SmoothSite.homMk_left] at h
  dsimp only [SmoothSite.fieldBaseChange]
  rw [Category.assoc, h]
  apply pullback.hom_ext
  · simp only [Category.assoc,
      SmoothSite.baseChange_map_fst, fieldBaseChangeProjection_fst_assoc,
      fieldBaseChangeAmbientInclusion_fst_assoc]
    change _ ≫ A.projection ≫ f.left = _ ≫ A.targetProjection
    rw [hA]
  · simp only [Category.assoc,
      SmoothSite.baseChange_map_snd, fieldBaseChangeProjection_snd,
      fieldBaseChangeAmbientInclusion_snd]

/-- Every actual reduced new component has the graph relation in the new product. -/
theorem fieldBaseChangeComponentGenerator_graph (f : X ⟶ Y)
    (hA : A.projection ≫ f.left = A.targetProjection)
    (w : genericPoints (A.fieldBaseChangeSupport φ)) :
    (A.fieldBaseChangeComponentGenerator φ w).projection ≫
        ((SmoothSite.fieldBaseChange φ).map f).left =
      (A.fieldBaseChangeComponentGenerator φ w).targetProjection := by
  let j := (IntegralClosedSubscheme.pointClosure w.1).val.subschemeι ≫
    A.fieldBaseChangeInclusion φ
  apply (cancel_epi j.toImage).mp
  change j.toImage ≫ j.imageι ≫ pullback.fst _ _ ≫ _ =
    j.toImage ≫ j.imageι ≫ pullback.snd _ _
  simp only [← Category.assoc, Scheme.Hom.toImage_imageι]
  dsimp only [j]
  simp only [Category.assoc, fieldBaseChangeInclusion_fst_assoc,
    fieldBaseChangeInclusion_graph φ A f hA]

/-- Each new component retains the literal source image of the component before imaging. -/
theorem fieldBaseChangeComponentGenerator_range
    (w : genericPoints (A.fieldBaseChangeSupport φ)) :
    Set.range (A.fieldBaseChangeComponentGenerator φ w).projection =
      closure ({A.fieldBaseChangeProjection φ w.1} :
        Set ((SmoothSite.fieldBaseChange φ).obj X).left) := by
  change Set.range (((IntegralClosedSubscheme.pointClosure w.1).val.subschemeι ≫
    A.fieldBaseChangeInclusion φ).imageι ≫ pullback.fst _ _) = _
  rw [range_image_projection, Category.assoc, fieldBaseChangeInclusion_fst]
  exact A.fieldBaseChangeComponent_range φ w

end FiniteCorrespondenceGenerator

section GraphComponents

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L)
  {X Y : SmoothSite.overField k} (f : X ⟶ Y)
  (C : Set X.left) (hC : C ∈ irreducibleComponents X.left)

local notation "G" => componentGraphGeneratorOver f.left (MorphismProperty.Over.w f) C hC

/-- The pulled-back whole graph component has open source projection. -/
instance fieldBaseChangeGraphProjection_isOpenImmersion :
    IsOpenImmersion ((G).fieldBaseChangeProjection φ) :=
  MorphismProperty.of_isPullback
    ((G).fieldBaseChangeProjection_isPullback φ) inferInstance

/-- The whole new graph support is reduced even when it is no longer integral. -/
instance fieldBaseChangeGraphSupport_isReduced :
    IsReduced ((G).fieldBaseChangeSupport φ) :=
  isReduced_of_isOpenImmersion
    ((G).fieldBaseChangeProjection φ)

/-- Every actual new graph component is the graph on its entire new source component. -/
theorem fieldBaseChangeComponentGenerator_componentGraph
    (w : genericPoints ((G).fieldBaseChangeSupport φ)) :
    (G).fieldBaseChangeComponentGenerator φ w =
      componentGraphGeneratorOver ((SmoothSite.fieldBaseChange φ).map f).left
        (MorphismProperty.Over.w ((SmoothSite.fieldBaseChange φ).map f))
        (closure {((G).fieldBaseChangeProjection φ) w.1})
        ((G).fieldBaseChangeProjection_generic φ w) := by
  apply FiniteCorrespondenceGenerator.eq_of_graph_range_eq
    ((SmoothSite.fieldBaseChange φ).map f).left
    (MorphismProperty.Over.w ((SmoothSite.fieldBaseChange φ).map f))
  · exact FiniteCorrespondenceGenerator.fieldBaseChangeComponentGenerator_graph φ _ f
      (componentGraphGeneratorOver_projection_target _ _ _ _) w
  · exact componentGraphGeneratorOver_projection_target _ _ _ _
  · exact ((G).fieldBaseChangeComponentGenerator_range φ w).trans
      (componentGraphGeneratorOver_range _ _ _ _).symm

end GraphComponents

namespace FieldBaseChangeGraph
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Hom

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L)
  {X Y : SmoothSite.overField k} (f : X ⟶ Y)

local notation "G[" C "]" =>
  componentGraphGeneratorOver f.left (MorphismProperty.Over.w f) C.1 C.2

/-- An old source component together with an actual new generic point of its whole graph. -/
abbrev ComponentIndex :=
  (C : irreducibleComponents X.left) ×
    genericPoints ((componentGraphGeneratorOver f.left (MorphismProperty.Over.w f)
      C.1 C.2).fieldBaseChangeSupport φ)

/-- The source generic point of an actual new graph component. -/
def sourceGeneric (i : ComponentIndex φ f) :
    genericPoints ((SmoothSite.fieldBaseChange φ).obj X).left :=
  ⟨(G[i.1]).fieldBaseChangeProjection φ i.2.1,
    (G[i.1]).fieldBaseChangeProjection_generic φ i.2⟩

/-- Each new point belongs to the Cartesian preimage of its original source component. -/
theorem sourceGeneric_mem (i : ComponentIndex φ f) :
    pullback.fst X.hom (Spec.map (CommRingCat.ofHom φ)) (sourceGeneric φ f i).1 ∈ i.1.1 := by
  let A := componentGraphGeneratorOver f.left (MorphismProperty.Over.w f) i.1.1 i.1.2
  have h : A.fieldBaseChangeProjection φ i.2.1 ∈ Set.range (A.fieldBaseChangeProjection φ) :=
    ⟨i.2.1, rfl⟩
  rw [A.fieldBaseChangeProjection_range φ] at h
  simpa only [A, componentGraphGeneratorOver_range, Set.mem_preimage, sourceGeneric] using h

/-- Distinct original clopen components and distinct points never identify in the source. -/
theorem sourceGeneric_injective : Function.Injective (sourceGeneric φ f) := by
  rintro ⟨C, w⟩ ⟨D, z⟩ h
  have hval := congrArg Subtype.val h
  have hC := sourceGeneric_mem φ f ⟨C, w⟩
  have hD := sourceGeneric_mem φ f ⟨D, z⟩
  rw [hval] at hC
  have hCD : C = D := by
    apply Subtype.ext
    by_contra hne
    exact Set.disjoint_left.mp
      (SmoothSite.pairwiseDisjoint_irreducibleComponents k X C.2 D.2 hne) hC hD
  subst D
  have hwz : w = z := by
    apply Subtype.ext
    exact ((G[C]).fieldBaseChangeProjection φ).isEmbedding.injective hval
  subst z
  rfl

/-- Every new source generic occurs, without assuming any old component stays integral. -/
theorem sourceGeneric_surjective : Function.Surjective (sourceGeneric φ f) := by
  intro x
  let p := pullback.fst X.hom (Spec.map (CommRingCat.ofHom φ))
  let C : irreducibleComponents X.left :=
    ⟨irreducibleComponent (p x.1), irreducibleComponent_mem_irreducibleComponents _⟩
  let A := componentGraphGeneratorOver f.left (MorphismProperty.Over.w f) C.1 C.2
  have hx : x.1 ∈ Set.range (A.fieldBaseChangeProjection φ) := by
    rw [A.fieldBaseChangeProjection_range φ]
    change p x.1 ∈ Set.range A.projection
    rw [componentGraphGeneratorOver_range]
    exact mem_irreducibleComponent
  obtain ⟨w, hw⟩ := hx
  have hwgen : w ∈ genericPoints (A.fieldBaseChangeSupport φ) :=
    mem_genericPoints_of_image_generic (A.fieldBaseChangeProjection φ) w (hw.symm ▸ x.2)
  exact ⟨⟨C, ⟨w, hwgen⟩⟩, Subtype.ext hw⟩

/-- The entire partition of actual graph components by the original source components. -/
def sourceGenericEquiv : ComponentIndex φ f ≃
    genericPoints ((SmoothSite.fieldBaseChange φ).obj X).left :=
  Equiv.ofBijective (sourceGeneric φ f)
    ⟨sourceGeneric_injective φ f, sourceGeneric_surjective φ f⟩

end FieldBaseChangeGraph

section GraphSums

variable {k : Type u} [Field k] {X Y : SmoothSite.overField k} (f : X ⟶ Y)

/-- The existing whole graph cycle as a sum over the actual source components. -/
theorem componentGraphCycleOver_eq_component_sum :
    componentGraphCycleOver f.left (MorphismProperty.Over.w f) =
      letI := (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
        (α := X.left)).fintype
      ∑ C : irreducibleComponents X.left,
        (componentGraphGeneratorOver f.left (MorphismProperty.Over.w f) C.1 C.2).cycle := by
  classical
  let := (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
    (α := X.left)).fintype
  rw [componentGraphCycleOver_eq_sum]
  rw [Finset.sum_subtype (p := fun C => C ∈ irreducibleComponents X.left) _
    (fun C => Set.Finite.mem_toFinset _)]
  apply Finset.sum_congr rfl
  intro C _
  rw [dite_eq_left C.2]

/-- The whole graph also enumerates all actual source generic points. -/
theorem componentGraphCycleOver_eq_generic_sum :
    componentGraphCycleOver f.left (MorphismProperty.Over.w f) =
      letI := IntegralCycle.genericPointFintype X.left
      ∑ x : genericPoints X.left,
        (componentGraphGeneratorOver f.left (MorphismProperty.Over.w f)
          (closure {x.1}) x.2).cycle := by
  classical
  let := IntegralCycle.genericPointFintype X.left
  let := (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
    (α := X.left)).fintype
  rw [componentGraphCycleOver_eq_component_sum]
  exact (Fintype.sum_equiv (genericPoints.equiv (α := X.left)) _ _ (fun _ => rfl)).symm

end GraphSums

namespace FiniteCorrespondence
open _root_.AlgebraicGeometry.Scheme

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L)
  {X Y : SmoothSite.overField k}

/-- Arbitrary field change preserves the full actual graph on any smooth source. -/
theorem fieldBaseChange_componentGraphCycleOver (f : X ⟶ Y) :
    fieldBaseChange (X := X) (Y := Y) φ
        (componentGraphCycleOver f.left (MorphismProperty.Over.w f)) =
      componentGraphCycleOver ((SmoothSite.fieldBaseChange φ).map f).left
        (MorphismProperty.Over.w ((SmoothSite.fieldBaseChange φ).map f)) := by
  classical
  let := (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
    (α := X.left)).fintype
  let (C : irreducibleComponents X.left) := IntegralCycle.genericPointFintype
    (FiniteCorrespondenceGenerator.fieldBaseChangeSupport φ
      (componentGraphGeneratorOver (X := X.left) (Y := Y.left) f.left
        (MorphismProperty.Over.w f) C.1 C.2))
  let := IntegralCycle.genericPointFintype ((SmoothSite.fieldBaseChange φ).obj X).left
  let H (x : genericPoints ((SmoothSite.fieldBaseChange φ).obj X).left) :=
    (componentGraphGeneratorOver ((SmoothSite.fieldBaseChange φ).map f).left
      (MorphismProperty.Over.w ((SmoothSite.fieldBaseChange φ).map f))
      (closure {x.1}) x.2).cycle
  calc
    _ = ∑ i : FieldBaseChangeGraph.ComponentIndex φ f,
        H (FieldBaseChangeGraph.sourceGeneric φ f i) := by
      rw [componentGraphCycleOver_eq_component_sum, map_sum, Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro C _
      rw [fieldBaseChange_cycle, FiniteCorrespondenceGenerator.fieldBaseChangeCycle_eq_sum]
      apply Finset.sum_congr rfl
      intro w _
      rw [genericMultiplicity_eq_one, Nat.cast_one,
        fieldBaseChangeComponentGenerator_componentGraph]
      rfl
    _ = ∑ x, H x := (FieldBaseChangeGraph.sourceGenericEquiv φ f).sum_comp H
    _ = _ := (componentGraphCycleOver_eq_generic_sum ((SmoothSite.fieldBaseChange φ).map f)).symm

@[simp] theorem fieldBaseChange_componentGraphCycleOver_simp (f : X ⟶ Y) :
    @DFunLike.coe
      (FiniteCorrespondence X.hom Y.hom →+
        FiniteCorrespondence (pullback.snd X.hom (Spec.map (CommRingCat.ofHom φ)))
          (pullback.snd Y.hom (Spec.map (CommRingCat.ofHom φ))))
      _ _ _ (fieldBaseChange (X := X) (Y := Y) φ)
        (componentGraphCycleOver f.left (MorphismProperty.Over.w f)) =
      componentGraphCycleOver ((SmoothSite.fieldBaseChange φ).map f).left
        (MorphismProperty.Over.w ((SmoothSite.fieldBaseChange φ).map f)) :=
  fieldBaseChange_componentGraphCycleOver φ f

/-- The entire diagonal, including every disconnected component, is preserved. -/
theorem fieldBaseChange_componentIdentityCycle (X : SmoothSite.overField k) :
    fieldBaseChange (X := X) (Y := X) φ (componentIdentityCycle X.hom) =
      componentIdentityCycle ((SmoothSite.fieldBaseChange φ).obj X).hom := by
  have h := fieldBaseChange_componentGraphCycleOver φ (𝟙 X)
  rw [(SmoothSite.fieldBaseChange φ).map_id] at h
  exact h

@[simp] theorem fieldBaseChange_componentIdentityCycle_simp (X : SmoothSite.overField k) :
    @DFunLike.coe
      (FiniteCorrespondence X.hom X.hom →+
        FiniteCorrespondence (pullback.snd X.hom (Spec.map (CommRingCat.ofHom φ)))
          (pullback.snd X.hom (Spec.map (CommRingCat.ofHom φ))))
      _ _ _ (fieldBaseChange (X := X) (Y := X) φ) (componentIdentityCycle X.hom) =
      componentIdentityCycle ((SmoothSite.fieldBaseChange φ).obj X).hom :=
  fieldBaseChange_componentIdentityCycle φ X

end FiniteCorrespondence

end Motivic
