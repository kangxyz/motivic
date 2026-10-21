/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Graph.Components.Composition
public import Motivic.AlgebraicGeometry.Correspondences.Graph.Flat.LeftComposition

/-!
# Whole pullbacks selected by a source graph component

For a section into a smooth object, an integral right support has its source
image in one component of the smooth source. The graph component containing
that image has the whole original support pullback as its incidence scheme.
Other source graph components have empty incidence. These are actual scheme
maps and open isomorphisms; no right-support flatness is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X Y Z : SmoothSite (Spec (.of k))}
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (φ : X.left ⟶ Y.left) (wφ : φ ≫ Y.hom = X.hom)
  (C : Set X.left) (hC : C ∈ irreducibleComponents X.left)

/-- The Noetherian instance used in this module. -/
local instance componentsPullbackNoetherian : IsNoetherian ((𝟭 Scheme).obj X.left) :=
  inferInstanceAs (IsNoetherian X.left)
/-- The reduced scheme instance used in this module. -/
local instance componentsPullbackReduced : IsReduced ((𝟭 Scheme).obj X.left) :=
  inferInstanceAs (IsReduced X.left)

/-- The original component incidence maps into the whole support pullback. -/
def componentGraphPullbackMap :
    (componentGraphGeneratorOver (X := X.left) (Y := Y.left) φ wφ C hC).incidence B ⟶
      B.graphPullback φ :=
  pullback.map _ _ _ _
    (componentGraphGeneratorOver (X := X.left) (Y := Y.left) φ wφ C hC).projection
    (𝟙 B.scheme) (𝟙 Y.left)
    (by simpa only [Category.comp_id] using
      (componentGraphGeneratorOver_projection_target (X := X.left) (Y := Y.left)
        φ wφ C hC).symm) (by simp)

instance componentGraphPullbackMap_open :
    IsOpenImmersion (B.componentGraphPullbackMap φ wφ C hC) := by
  unfold componentGraphPullbackMap
  infer_instance

@[reassoc (attr := simp)]
theorem componentGraphPullbackMap_fst :
    B.componentGraphPullbackMap φ wφ C hC ≫ pullback.fst φ B.projection =
      (componentGraphGeneratorOver (X := X.left) (Y := Y.left) φ wφ C hC).incidenceFst B ≫
        (componentGraphGeneratorOver (X := X.left) (Y := Y.left) φ wφ C hC).projection := by
  simp only [componentGraphPullbackMap, pullback.map, pullback.lift_fst]

@[reassoc (attr := simp)]
theorem componentGraphPullbackMap_snd :
    B.componentGraphPullbackMap φ wφ C hC ≫ pullback.snd φ B.projection =
      (componentGraphGeneratorOver (X := X.left) (Y := Y.left) φ wφ C hC).incidenceSnd B := by
  simp only [componentGraphPullbackMap, pullback.map, pullback.lift_snd, Category.comp_id]

/-- The actual source-target map is unchanged by the component comparison. -/
theorem componentGraphPullbackMap_incidenceMap :
    B.componentGraphPullbackMap φ wφ C hC ≫ B.graphPullbackMap φ wφ =
      (componentGraphGeneratorOver (X := X.left) (Y := Y.left) φ wφ C hC).incidenceMap B := by
  apply pullback.hom_ext <;> simp

variable (q : Y.left ⟶ X.left) (hsection : φ ≫ q = 𝟙 X.left)

include hsection in
/-- If the integral right support lands in this source component, its entire
pullback is the actual graph-component incidence, including nilpotents. -/
theorem componentGraphPullbackMap_isIso
    (hB : Set.range (B.projection ≫ q) ⊆ C) :
    IsIso (B.componentGraphPullbackMap φ wφ C hC) := by
  apply (isIso_iff_isOpenImmersion_and_surjective _).mpr
  refine ⟨inferInstance, ⟨Set.range_eq_univ.mp ?_⟩⟩
  unfold componentGraphPullbackMap
  rw [Scheme.Pullback.range_map]
  apply Set.eq_univ_of_forall
  intro z
  refine ⟨?_, ⟨pullback.snd φ B.projection z, rfl⟩⟩
  change pullback.fst φ B.projection z ∈
    Set.range (componentGraphGeneratorOver (X := X.left) (Y := Y.left) φ wφ C hC).projection
  rw [componentGraphGeneratorOver_range]
  have hz := hB ⟨pullback.snd φ B.projection z, rfl⟩
  have heq : pullback.snd φ B.projection ≫ B.projection ≫ q =
      pullback.fst φ B.projection := by
    rw [← Category.assoc, ← pullback.condition, Category.assoc, hsection, Category.comp_id]
  have he := congrArg (fun p ↦ p z) heq
  exact he ▸ hz

include hsection in
/-- Different clopen source components give genuinely empty incidence. -/
theorem componentGraph_incidence_isEmpty_of_ne
    (D : Set X.left) (hD : D ∈ irreducibleComponents X.left)
    (hB : Set.range (B.projection ≫ q) ⊆ D) (hne : C ≠ D) :
    IsEmpty ((componentGraphGeneratorOver (X := X.left) (Y := Y.left) φ wφ C hC).incidence B) := by
  constructor
  intro z
  apply hne
  let F := componentGraphGeneratorOver (X := X.left) (Y := Y.left) φ wφ C hC
  have hleft : F.projection (F.incidenceFst B z) ∈ C := by
    rw [← componentGraphGeneratorOver_range φ wφ C hC]
    exact Set.mem_range_self _
  have hright := hB ⟨F.incidenceSnd B z, rfl⟩
  have heq : F.incidenceFst B ≫ F.projection = F.incidenceSnd B ≫ B.projection ≫ q := by
    rw [← Category.assoc, ← F.incidence_condition B, Category.assoc]
    change _ = F.incidenceFst B ≫ F.targetProjection ≫ q
    rw [← componentGraphGeneratorOver_projection_target, Category.assoc, hsection,
      Category.comp_id]
  have he := congrArg (fun p ↦ p z) heq
  exact irreducibleComponents_eq_of_mem_of_domain_stalks
    (fun x ↦ SmoothSite.isDomain_stalk k X x) hC hD hleft (he.symm ▸ hright)

omit C hC φ wφ hsection in
/-- The original integral support's projected image lies in an actual source
component. This uses only irreducibility of the support, not projection flatness. -/
theorem exists_sourceComponent_of_integral :
    ∃ C ∈ irreducibleComponents X.left, Set.range (B.projection ≫ q) ⊆ C := by
  apply exists_mem_irreducibleComponents_subset_of_isIrreducible
  simpa only [Set.image_univ] using
    (IrreducibleSpace.isIrreducible_univ B.scheme).image (B.projection ≫ q)
      (B.projection ≫ q).continuous.continuousOn

omit C hC φ wφ hsection in
/-- Disjoint smooth-source components make the selected containing component unique. -/
theorem existsUnique_sourceComponent_of_integral :
    ∃! C : Set X.left, C ∈ irreducibleComponents X.left ∧
      Set.range (B.projection ≫ q) ⊆ C := by
  obtain ⟨D, hD, hB⟩ := B.exists_sourceComponent_of_integral q
  refine ⟨D, ⟨hD, hB⟩, ?_⟩
  intro C hC
  let z := genericPoint B.scheme
  exact irreducibleComponents_eq_of_mem_of_domain_stalks
    (fun x ↦ SmoothSite.isDomain_stalk k X x) hC.1 hD
    (hC.2 (Set.mem_range_self z)) (hB (Set.mem_range_self z))

end Motivic.FiniteCorrespondenceGenerator
