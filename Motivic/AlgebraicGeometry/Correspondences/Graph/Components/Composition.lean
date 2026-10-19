/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Identity.Units

/-!
# Composition of actual component graph cycles

The source projection of each graph component on a smooth scheme is an open
immersion. Its incidence with a second graph component is either empty or
isomorphic to the first component. In the surviving case, the source-target
map is the composed graph, and the genuine Tor coefficient agrees with the
ordinary fundamental multiplicity. Summing these actual component calculations
gives graph composition for arbitrary disconnected smooth objects.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

section
open _root_.AlgebraicGeometry.Scheme

section ComponentGeometry

variable {S X Y Z : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S}
  [IsNoetherian X] [IsReduced X] [IsSeparated g] [IsSeparated h]
  (φ : X ⟶ Y) (wφ : φ ≫ g = f) (ψ : Y ⟶ Z) (wψ : ψ ≫ h = g)
  (C : Set X) (hC : C ∈ irreducibleComponents X)

/-- The actual component graph support is isomorphic to its source component. -/
noncomputable def _root_.Motivic.componentGraphSchemeIso :
    X.irreducibleComponent C hC ≅ (_root_.Motivic.componentGraphGeneratorOver φ wφ C hC).scheme :=
        by
  subst f
  change X.irreducibleComponent C hC ≅ (_root_.Motivic.componentGraph φ g C hC).image
  have : IsIso (_root_.Motivic.componentGraph φ g C hC).toImage :=
    IsClosedImmersion.instIsIsoSchemeToImage _
  exact asIso (_root_.Motivic.componentGraph φ g C hC).toImage

@[reassoc (attr := simp)]
theorem _root_.Motivic.componentGraphSchemeIso_hom_projection :
    (_root_.Motivic.componentGraphSchemeIso φ wφ C hC).hom ≫
      (_root_.Motivic.componentGraphGeneratorOver φ wφ C hC).projection =
        X.irreducibleComponentι C hC := by
  subst f
  change (_root_.Motivic.componentGraph φ g C hC).toImage ≫
    _root_.Motivic.correspondenceProjection (φ ≫ g) g (_root_.Motivic.componentGraphIdeal φ g C hC)
        = _
  exact _root_.Motivic.componentGraph_toImage_projection φ g C hC

@[reassoc (attr := simp)]
theorem _root_.Motivic.componentGraphSchemeIso_hom_targetProjection :
    (_root_.Motivic.componentGraphSchemeIso φ wφ C hC).hom ≫
      (_root_.Motivic.componentGraphGeneratorOver φ wφ C hC).targetProjection =
        X.irreducibleComponentι C hC ≫ φ := by
  rw [← _root_.Motivic.componentGraphGeneratorOver_projection_target, ← Category.assoc,
    _root_.Motivic.componentGraphSchemeIso_hom_projection]

/-- Postcomposing a component graph replaces its target map without changing its support. -/
noncomputable def _root_.Motivic.componentGraphPostcompositionIso :
    (_root_.Motivic.componentGraphGeneratorOver φ wφ C hC).scheme ≅
      (_root_.Motivic.componentGraphGeneratorOver (f := f) (g := h) (φ ≫ ψ) (by rw [Category.assoc,
          wψ, wφ]) C
        hC).scheme :=
  (_root_.Motivic.componentGraphSchemeIso φ wφ C hC).symm ≪≫
    _root_.Motivic.componentGraphSchemeIso (f := f) (g := h) (φ ≫ ψ) (by rw [Category.assoc, wψ,
        wφ]) C hC

/-- The actual postcomposition map is the composed component graph closed immersion. -/
theorem _root_.Motivic.componentGraphPostcompositionMap_eq :
    (_root_.Motivic.componentGraphGeneratorOver φ wφ C hC).graphPostcompositionMap ψ wψ =
      (_root_.Motivic.componentGraphPostcompositionIso φ wφ ψ wψ C hC).hom ≫
        (_root_.Motivic.componentGraphGeneratorOver (f := f) (g := h) (φ ≫ ψ)
          (by rw [Category.assoc, wψ, wφ]) C hC).inclusion := by
  apply (cancel_epi (_root_.Motivic.componentGraphSchemeIso φ wφ C hC).hom).mp
  apply pullback.hom_ext
  · simp only [Category.assoc,
      _root_.Motivic.FiniteCorrespondenceGenerator.graphPostcompositionMap_fst]
    change _ = _ ≫ _ ≫
      (_root_.Motivic.componentGraphGeneratorOver (f := f) (g := h) (φ ≫ ψ)
        (by rw [Category.assoc, wψ, wφ]) C hC).projection
    simp [_root_.Motivic.componentGraphPostcompositionIso]
  · simp only [Category.assoc,
      _root_.Motivic.FiniteCorrespondenceGenerator.graphPostcompositionMap_snd]
    change _ = _ ≫ _ ≫
      (_root_.Motivic.componentGraphGeneratorOver (f := f) (g := h) (φ ≫ ψ)
        (by rw [Category.assoc, wψ, wφ]) C hC).targetProjection
    simp [_root_.Motivic.componentGraphPostcompositionIso]

end ComponentGeometry

section SmoothGeometry

local instance {k : Type u} [Field k] (T : SmoothSite (Spec (.of k))) : IsNoetherian ((𝟭
  Scheme).obj T.left) :=
  inferInstanceAs (IsNoetherian T.left)

local instance {k : Type u} [Field k] (T : SmoothSite (Spec (.of k))) : IsReduced ((𝟭
  Scheme).obj T.left) :=
  inferInstanceAs (IsReduced T.left)

namespace AlgebraicGeometry.Scheme.SmoothSite

variable (k : Type u) [Field k] {X Y : SmoothSite (Spec (.of k))}

/-- A smooth component graph has open source projection, including on disconnected sources. -/
instance componentGraphGeneratorOver_projection_isOpenImmersion
    (φ : X.left ⟶ Y.left) (wφ : φ ≫ Y.hom = X.hom)
    (C : Set X.left) (hC : C ∈ irreducibleComponents X.left) :
    IsOpenImmersion (_root_.Motivic.componentGraphGeneratorOver (X := X.left) (Y := Y.left) φ wφ C
      hC).projection :=
  Motivic.componentGraphGeneratorOver_projection_isOpenImmersion
    (pairwiseDisjoint_irreducibleComponents k X) φ wφ C hC

end AlgebraicGeometry.Scheme.SmoothSite

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] {X Y Z : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (ψ : Y.left ⟶ Z.left) (wψ : ψ ≫ Z.hom = Y.hom)

/-- The source-target map of component graph incidence is the postcomposed support map. -/
theorem incidenceMap_componentGraph_right
    (D : Set Y.left) (hD : D ∈ irreducibleComponents Y.left) :
    A.incidenceMap (componentGraphGeneratorOver (X := Y.left) (Y := Z.left) (f := Y.hom) (g :=
      Z.hom) ψ wψ D hD) =
      A.incidenceFst (componentGraphGeneratorOver (X := Y.left) (Y := Z.left) (f := Y.hom) (g
        := Z.hom) ψ wψ D hD) ≫
        A.graphPostcompositionMap ψ wψ := by
  apply pullback.hom_ext
  · simp only [incidenceMap_fst, Category.assoc, graphPostcompositionMap_fst]
  · simp only [incidenceMap_snd, Category.assoc, graphPostcompositionMap_snd]
    change A.incidenceSnd (componentGraphGeneratorOver (X := Y.left) (Y := Z.left) (f := Y.hom)
      (g := Z.hom) ψ wψ D hD) ≫
        (componentGraphGeneratorOver (X := Y.left) (Y := Z.left) (f := Y.hom) (g := Z.hom) ψ wψ
          D hD).targetProjection =
      A.incidenceFst (componentGraphGeneratorOver (X := Y.left) (Y := Z.left) (f := Y.hom) (g
        := Z.hom) ψ wψ D hD) ≫ A.targetProjection ≫ ψ
    rw [← componentGraphGeneratorOver_projection_target, ← Category.assoc,
      ← A.incidence_condition, Category.assoc]

/-- The unique compatible middle component gives an incidence isomorphism. -/
theorem isIso_incidenceFst_componentGraph
    (D : Set Y.left) (hD : D ∈ irreducibleComponents Y.left)
    (hA : Set.range A.targetProjection ⊆ D) :
    IsIso (A.incidenceFst (componentGraphGeneratorOver (X := Y.left) (Y := Z.left) (f := Y.hom)
      (g := Z.hom) ψ wψ D hD)) := by
  have : IsOpenImmersion (A.incidenceFst (componentGraphGeneratorOver (X := Y.left) (Y :=
    Z.left) (f := Y.hom) (g := Z.hom) ψ wψ D hD)) :=
    inferInstanceAs (IsOpenImmersion (pullback.fst A.targetProjection
      (componentGraphGeneratorOver (X := Y.left) (Y := Z.left) (f := Y.hom) (g := Z.hom) ψ wψ D
        hD).projection))
  apply (isIso_iff_isOpenImmersion_and_surjective _).mpr
  refine ⟨inferInstance, ⟨A.incidenceFst_surjective _ ?_⟩⟩
  simpa only [componentGraphGeneratorOver_range] using hA

/-- An incompatible middle component contributes zero to actual graph composition. -/
theorem incidenceTorCorrespondence_componentGraph_right_of_ne
    (D E : Set Y.left) (hD : D ∈ irreducibleComponents Y.left)
    (hE : E ∈ irreducibleComponents Y.left)
    (hA : Set.range A.targetProjection ⊆ E) (hne : E ≠ D) :
    A.incidenceTorCorrespondence k (Z := Z) (componentGraphGeneratorOver (X := Y.left) (Y :=
      Z.left) (f := Y.hom) (g := Z.hom) ψ wψ D hD) = 0 := by
  have : IsEmpty (A.incidence (componentGraphGeneratorOver (X := Y.left) (Y := Z.left) (f :=
    Y.hom) (g := Z.hom) ψ wψ D hD)) :=
    A.incidence_isEmpty_of_distinct_component k _ E hE hA (by
      simpa only [componentGraphGeneratorOver_range] using hne)
  exact A.incidenceTorCorrespondence_eq_zero_of_isEmpty k _

end Motivic.FiniteCorrespondenceGenerator

section Composition

variable (k : Type u) [Field k] {X Y Z : SmoothSite (Spec (.of k))}
  (φ : X.left ⟶ Y.left) (wφ : φ ≫ Y.hom = X.hom)
  (ψ : Y.left ⟶ Z.left) (wψ : ψ ≫ Z.hom = Y.hom)

/-- Surviving actual component graph incidence is the composed graph with coefficient one. -/
theorem _root_.Motivic.incidenceTorCorrespondence_componentGraph_comp
    (C : Set X.left) (hC : C ∈ irreducibleComponents X.left)
    (D : Set Y.left) (hD : D ∈ irreducibleComponents Y.left)
    (hA : Set.range (_root_.Motivic.componentGraphGeneratorOver (X := X.left) (Y := Y.left) φ wφ C
      hC).targetProjection ⊆ D) :
    (_root_.Motivic.componentGraphGeneratorOver (X := X.left) (Y := Y.left) φ wφ C
      hC).incidenceTorCorrespondence k (Z := Z)
      (_root_.Motivic.componentGraphGeneratorOver (X := Y.left) (Y := Z.left) (f := Y.hom) (g :=
          Z.hom) ψ wψ D
        hD) =
        (_root_.Motivic.componentGraphGeneratorOver (X := X.left) (Y := Z.left) (f := X.hom) (g :=
            Z.hom) (φ ≫ ψ)
          (by rw [Category.assoc, wψ, wφ]) C hC).cycle := by
  let A := _root_.Motivic.componentGraphGeneratorOver (X := X.left) (Y := Y.left) φ wφ C hC
  let B := _root_.Motivic.componentGraphGeneratorOver (X := Y.left) (Y := Z.left) (f := Y.hom) (g :=
      Z.hom) ψ
    wψ D hD
  let E := _root_.Motivic.componentGraphGeneratorOver (X := X.left) (Y := Z.left) (f := X.hom) (g :=
      Z.hom) (φ ≫ ψ)
    (by rw [Category.assoc, wψ, wφ]) C hC
  have : IsIso (A.incidenceFst B) :=
    A.isIso_incidenceFst_componentGraph k ψ wψ D hD hA
  have : IsNoetherian A.scheme := isNoetherian_of_finiteType A.projection
  have : IsNoetherian E.scheme := isNoetherian_of_finiteType E.projection
  have : IsNoetherian (pullback X.hom Z.hom) :=
    isNoetherian_of_finiteType (pullback.fst X.hom Z.hom)
  change A.incidenceTorCorrespondence k (Z := Z) B = E.cycle
  rw [A.incidenceTorCorrespondence_eq_fundamental_of_isOpenImmersion_projection k B]
  apply _root_.Motivic.FiniteCorrespondence.toIntegralCycle_injective
  rw [A.toIntegralCycle_incidenceFundamentalCorrespondence k B]
  simp only [B, A.incidenceMap_componentGraph_right k ψ wψ D hD,
    IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply,
    finitePushforward_fundamentalCycle]
  simp only [A, _root_.Motivic.componentGraphPostcompositionMap_eq φ wφ ψ wψ C hC,
    IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply,
    finitePushforward_fundamentalCycle]
  rw [_root_.Motivic.FiniteCorrespondenceGenerator.cycle,
      _root_.Motivic.FiniteCorrespondence.toIntegralCycle_single]
  change closedFundamentalCycle E.val = Finsupp.single E.toIntegralClosedSubscheme 1
  rw [closedFundamentalCycle_of_isIntegral]
  rfl

/-- Composing one graph component with the full second graph keeps exactly its composed graph. -/
theorem _root_.Motivic.incidenceTorPairing_componentGraph_cycle
    (C : Set X.left) (hC : C ∈ irreducibleComponents X.left) :
    _root_.Motivic.FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := Z)
      (_root_.Motivic.componentGraphGeneratorOver (X := X.left) (Y := Y.left) φ wφ C hC).cycle
        (_root_.Motivic.componentGraphCycleOver (X := Y.left) (Y := Z.left) ψ wψ) =
        (_root_.Motivic.componentGraphGeneratorOver (X := X.left) (Y := Z.left) (f := X.hom) (g :=
            Z.hom) (φ ≫ ψ)
          (by rw [Category.assoc, wψ, wφ]) C hC).cycle := by
  classical
  let A := _root_.Motivic.componentGraphGeneratorOver (X := X.left) (Y := Y.left) φ wφ C hC
  obtain ⟨D, hD, hA⟩ : ∃ D ∈ irreducibleComponents Y.left,
      Set.range A.targetProjection ⊆ D :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible
      (Set.range A.targetProjection) (by
        simpa only [Set.image_univ] using
          (IrreducibleSpace.isIrreducible_univ A.scheme).image
            A.targetProjection A.targetProjection.continuous.continuousOn)
  rw [_root_.Motivic.componentGraphCycleOver_eq_sum]
  simp only [map_sum]
  rw [Finset.sum_eq_single (ι := Set Y.left) D]
  · rw [dite_eq_left hD, _root_.Motivic.FiniteCorrespondence.incidenceTorPairing_cycle]
    exact _root_.Motivic.incidenceTorCorrespondence_componentGraph_comp k φ wφ ψ wψ C hC D hD hA
  · intro E hE hED
    have hE' : E ∈ irreducibleComponents Y.left := by simpa using hE
    rw [dite_eq_left hE', _root_.Motivic.FiniteCorrespondence.incidenceTorPairing_cycle]
    exact A.incidenceTorCorrespondence_componentGraph_right_of_ne k ψ wψ E D hE' hD hA
      hED.symm
  · intro hnot
    exact (hnot (by simpa using hD)).elim

/-- Actual componentwise graph cycles compose for arbitrary smooth separated finite-type objects. -/
theorem _root_.Motivic.incidenceTorPairing_componentGraph_comp :
    _root_.Motivic.FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := Z)
      (_root_.Motivic.componentGraphCycleOver (X := X.left) (Y := Y.left) φ wφ)
          (_root_.Motivic.componentGraphCycleOver (X :=
        Y.left) (Y := Z.left) ψ wψ) =
        _root_.Motivic.componentGraphCycleOver (X := X.left) (Y := Z.left) (f := X.hom) (g := Z.hom)
            (φ ≫ ψ)
          (by rw [Category.assoc, wψ, wφ]) := by
  classical
  change (_root_.Motivic.FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := Z)).flip
    (_root_.Motivic.componentGraphCycleOver (X := Y.left) (Y := Z.left) ψ wψ)
        (_root_.Motivic.componentGraphCycleOver (X :=
      X.left) (Y := Y.left) φ wφ) = _
  rw [_root_.Motivic.componentGraphCycleOver_eq_sum (X := X.left) (Y := Y.left) φ wφ,
    _root_.Motivic.componentGraphCycleOver_eq_sum (X := X.left) (Y := Z.left)
      (f := X.hom) (g := Z.hom) (φ ≫ ψ)]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro C hC
  have hC' : C ∈ irreducibleComponents X.left := by simpa using hC
  simp only [dite_eq_left hC']
  exact _root_.Motivic.incidenceTorPairing_componentGraph_cycle k φ wφ ψ wψ C hC'

end Composition

end SmoothGeometry

end
