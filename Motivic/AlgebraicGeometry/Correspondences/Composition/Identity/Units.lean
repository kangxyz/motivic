/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Identity.Tor
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Actual diagonal component incidence and full identity laws

The surviving diagonal component incidence is isomorphic to the original
integral support. Incompatible components have empty incidence. Together
with the proved genuine Tor comparison these geometric calculations give
the units of the actual biadditive incidence operation on arbitrary smooth
objects, including disconnected and empty objects.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic

section Transport

variable {S X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
  [IsNoetherian X] [IsReduced X] [IsSeparated g]

/-- Structural transport retains the exact component image of the graph projection. -/
theorem componentGraphGeneratorOver_range (φ : X ⟶ Y) (w : φ ≫ g = f)
    (C : Set X) (hC : C ∈ irreducibleComponents X) :
    Set.range (componentGraphGeneratorOver φ w C hC).projection = C := by
  subst f
  exact componentGraphGenerator_range φ g C hC

end Transport

section Identity

variable {S X : Scheme.{u}} (f : X ⟶ S)
  [IsNoetherian X] [IsReduced X] [IsSeparated f]

/-- The actual source image of a diagonal component is the specified component. -/
@[simp]
theorem componentIdentityGenerator_range (C : Set X)
    (hC : C ∈ irreducibleComponents X) :
    Set.range (componentIdentityGenerator f C hC).projection = C :=
  componentGraphGeneratorOver_range (𝟙 X) (Category.id_comp f) C hC

open Classical in
/-- The full actual identity is the finite sum of all genuine diagonal components. -/
theorem componentIdentityCycle_eq_sum :
    componentIdentityCycle f =
      ∑ C ∈ TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.toFinset,
        if hC : C ∈ irreducibleComponents X then
          (componentIdentityGenerator f C hC).cycle else 0 :=
  componentGraphCycleOver_eq_sum (𝟙 X) (Category.id_comp f)

end Identity

namespace FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] {X Y : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)

/-- Right component incidence maps by its first projection followed by the original support. -/
theorem incidenceMap_componentIdentity_right
    (C : Set Y.left) (hC : C ∈ irreducibleComponents Y.left) :
    A.incidenceMap (componentIdentityGenerator (X := Y.left) Y.hom C hC) =
      A.incidenceFst (componentIdentityGenerator (X := Y.left) Y.hom C hC) ≫ A.inclusion := by
  apply pullback.hom_ext
  · simp only [incidenceMap_fst, Category.assoc]
    rfl
  · simp only [incidenceMap_snd, Category.assoc]
    change A.incidenceSnd (componentIdentityGenerator (X := Y.left) Y.hom C hC) ≫
        (componentIdentityGenerator (X := Y.left) Y.hom C hC).targetProjection =
      A.incidenceFst (componentIdentityGenerator (X := Y.left) Y.hom C hC) ≫ A.targetProjection
    rw [componentIdentityGenerator_targetProjection, A.incidence_condition]

/-- Left component incidence maps by its second projection followed by the original support. -/
theorem incidenceMap_componentIdentity_left
    (C : Set X.left) (hC : C ∈ irreducibleComponents X.left) :
    (componentIdentityGenerator (X := X.left) X.hom C hC).incidenceMap A =
      (componentIdentityGenerator (X := X.left) X.hom C hC).incidenceSnd A ≫ A.inclusion := by
  apply pullback.hom_ext
  · simp only [incidenceMap_fst, Category.assoc]
    change (componentIdentityGenerator (X := X.left) X.hom C hC).incidenceFst A ≫
        (componentIdentityGenerator (X := X.left) X.hom C hC).projection =
      (componentIdentityGenerator (X := X.left) X.hom C hC).incidenceSnd A ≫ A.projection
    rw [← componentIdentityGenerator_targetProjection, incidence_condition]
  · simp only [incidenceMap_snd, Category.assoc]

/-- The surviving right diagonal component has incidence isomorphic to the original support. -/
theorem isIso_incidenceFst_componentIdentity
    (C : Set Y.left) (hC : C ∈ irreducibleComponents Y.left)
    (hA : Set.range A.targetProjection ⊆ C) :
    IsIso (A.incidenceFst (componentIdentityGenerator (X := Y.left) Y.hom C hC)) := by
  have : IsOpenImmersion
      (A.incidenceFst (componentIdentityGenerator (X := Y.left) Y.hom C hC)) :=
    inferInstanceAs (IsOpenImmersion (pullback.fst A.targetProjection
      (componentIdentityGenerator (X := Y.left) Y.hom C hC).projection))
  apply (isIso_iff_isOpenImmersion_and_surjective _).mpr
  refine ⟨inferInstance, ⟨A.incidenceFst_surjective _ ?_⟩⟩
  simpa only [componentIdentityGenerator_range] using hA

/-- The surviving left diagonal component has incidence isomorphic to the original support. -/
theorem isIso_incidenceSnd_componentIdentity
    (C : Set X.left) (hC : C ∈ irreducibleComponents X.left)
    (hA : Set.range A.projection = C) :
    IsIso ((componentIdentityGenerator (X := X.left) X.hom C hC).incidenceSnd A) := by
  have : IsOpenImmersion
      ((componentIdentityGenerator (X := X.left) X.hom C hC).incidenceSnd A) :=
    inferInstanceAs (IsOpenImmersion (pullback.snd
      (componentIdentityGenerator (X := X.left) X.hom C hC).targetProjection A.projection))
  apply (isIso_iff_isOpenImmersion_and_surjective _).mpr
  refine ⟨inferInstance, ⟨Set.range_eq_univ.mp ?_⟩⟩
  change Set.range (pullback.snd
    (componentIdentityGenerator (X := X.left) X.hom C hC).targetProjection A.projection) = _
  rw [Scheme.Pullback.range_snd, componentIdentityGenerator_targetProjection,
    componentIdentityGenerator_range]
  exact Set.eq_univ_of_forall fun a ↦ hA ▸ Set.mem_range_self a

/-- The surviving right component is the original cycle under the actual Tor operation. -/
theorem incidenceTorCorrespondence_componentIdentity_right_of_range_subset
    (C : Set Y.left) (hC : C ∈ irreducibleComponents Y.left)
    (hA : Set.range A.targetProjection ⊆ C) :
    A.incidenceTorCorrespondence k (componentIdentityGenerator (X := Y.left) Y.hom C hC) =
      A.cycle := by
  have := A.isIso_incidenceFst_componentIdentity k C hC hA
  have : IsNoetherian ((𝟭 Scheme).obj X.left) := inferInstanceAs (IsNoetherian X.left)
  have : IsNoetherian A.scheme := isNoetherian_of_finiteType A.projection
  have : IsNoetherian (pullback X.hom Y.hom) :=
    isNoetherian_of_finiteType (pullback.fst X.hom Y.hom)
  rw [A.incidenceTorCorrespondence_componentIdentity_right k]
  apply FiniteCorrespondence.toIntegralCycle_injective
  rw [A.toIntegralCycle_incidenceFundamentalCorrespondence k]
  simp only [A.incidenceMap_componentIdentity_right k, IntegralCycle.finitePushforward_comp,
    AddMonoidHom.comp_apply]
  rw [finitePushforward_fundamentalCycle, FiniteCorrespondenceGenerator.cycle,
    FiniteCorrespondence.toIntegralCycle_single]
  change closedFundamentalCycle A.val = Finsupp.single A.toIntegralClosedSubscheme 1
  rw [closedFundamentalCycle_of_isIntegral]
  rfl

/-- The surviving left component is the original cycle under the actual Tor operation. -/
theorem incidenceTorCorrespondence_componentIdentity_left_of_range_eq
    (C : Set X.left) (hC : C ∈ irreducibleComponents X.left)
    (hA : Set.range A.projection = C) :
    (componentIdentityGenerator (X := X.left) X.hom C hC).incidenceTorCorrespondence k A =
      A.cycle := by
  have := A.isIso_incidenceSnd_componentIdentity k C hC hA
  have : IsNoetherian ((𝟭 Scheme).obj X.left) := inferInstanceAs (IsNoetherian X.left)
  have : IsNoetherian A.scheme := isNoetherian_of_finiteType A.projection
  have : IsNoetherian (pullback X.hom Y.hom) :=
    isNoetherian_of_finiteType (pullback.fst X.hom Y.hom)
  rw [A.incidenceTorCorrespondence_componentIdentity_left k]
  apply FiniteCorrespondence.toIntegralCycle_injective
  rw [toIntegralCycle_incidenceFundamentalCorrespondence k
      (componentIdentityGenerator (X := X.left) X.hom C hC)]
  simp only [A.incidenceMap_componentIdentity_left k, IntegralCycle.finitePushforward_comp,
    AddMonoidHom.comp_apply]
  rw [finitePushforward_fundamentalCycle, FiniteCorrespondenceGenerator.cycle,
    FiniteCorrespondence.toIntegralCycle_single]
  change closedFundamentalCycle A.val = Finsupp.single A.toIntegralClosedSubscheme 1
  rw [closedFundamentalCycle_of_isIntegral]
  rfl


/-- Empty actual incidence contributes zero to the genuine Tor correspondence. -/
theorem incidenceTorCorrespondence_eq_zero_of_isEmpty
    {Z : SmoothSite (Spec (.of k))}
    (B : FiniteCorrespondenceGenerator Y.hom Z.hom) [IsEmpty (A.incidence B)] :
    A.incidenceTorCorrespondence k B = 0 := by
  classical
  simp [incidenceTorCorrespondence, incidenceCycleAssembly]

/-- A different right diagonal component contributes no actual Tor cycle. -/
theorem incidenceTorCorrespondence_componentIdentity_right_of_ne
    (C D : Set Y.left) (hC : C ∈ irreducibleComponents Y.left)
    (hD : D ∈ irreducibleComponents Y.left)
    (hA : Set.range A.targetProjection ⊆ D) (hne : D ≠ C) :
    A.incidenceTorCorrespondence k (componentIdentityGenerator (X := Y.left) Y.hom C hC) =
      0 := by
  have : IsEmpty (A.incidence (componentIdentityGenerator (X := Y.left) Y.hom C hC)) :=
    A.incidence_isEmpty_of_distinct_component k _ D hD hA (by
      simpa only [componentIdentityGenerator_range] using hne)
  exact A.incidenceTorCorrespondence_eq_zero_of_isEmpty k _

/-- A different left diagonal component contributes no actual Tor cycle. -/
theorem incidenceTorCorrespondence_componentIdentity_left_of_ne
    (C : Set X.left) (hC : C ∈ irreducibleComponents X.left)
    (hne : C ≠ Set.range A.projection) :
    (componentIdentityGenerator (X := X.left) X.hom C hC).incidenceTorCorrespondence k A =
      0 := by
  have : IsEmpty ((componentIdentityGenerator (X := X.left) X.hom C hC).incidence A) :=
    incidence_isEmpty_of_distinct_component k
      (componentIdentityGenerator (X := X.left) X.hom C hC) A C hC (by
        rw [componentIdentityGenerator_targetProjection, componentIdentityGenerator_range]) hne
  exact incidenceTorCorrespondence_eq_zero_of_isEmpty k
    (componentIdentityGenerator (X := X.left) X.hom C hC) A

/-- The full actual smooth diagonal is a right unit on each genuine generator. -/
theorem incidenceTorPairing_componentIdentity_right_cycle :
    FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := Y)
      A.cycle (componentIdentityCycle (X := Y.left) Y.hom) = A.cycle := by
  classical
  obtain ⟨C, hC, hA⟩ : ∃ C ∈ irreducibleComponents Y.left,
      Set.range A.targetProjection ⊆ C :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible
      (Set.range A.targetProjection) (by
        simpa only [Set.image_univ] using
          (IrreducibleSpace.isIrreducible_univ A.scheme).image
            A.targetProjection A.targetProjection.continuous.continuousOn)
  rw [componentIdentityCycle_eq_sum]
  simp only [map_sum]
  rw [Finset.sum_eq_single (ι := Set Y.left) C]
  · rw [dite_eq_left hC, FiniteCorrespondence.incidenceTorPairing_cycle,
      A.incidenceTorCorrespondence_componentIdentity_right_of_range_subset k C hC hA]
  · intro D hD hDC
    have hD' : D ∈ irreducibleComponents Y.left := by simpa using hD
    rw [dite_eq_left hD', FiniteCorrespondence.incidenceTorPairing_cycle]
    exact A.incidenceTorCorrespondence_componentIdentity_right_of_ne k D C hD' hC hA hDC.symm
  · intro hnot
    exact (hnot (by simpa using hC)).elim

/-- The full actual smooth diagonal is a left unit on each genuine generator. -/
theorem incidenceTorPairing_componentIdentity_left_cycle :
    FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := X) (Z := Y)
      (componentIdentityCycle (X := X.left) X.hom) A.cycle = A.cycle := by
  classical
  change (FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := X) (Z := Y)).flip
    A.cycle (componentIdentityCycle (X := X.left) X.hom) = A.cycle
  rw [componentIdentityCycle_eq_sum]
  simp only [map_sum]
  have hAC : (Set.range A.projection : Set X.left) ∈ irreducibleComponents X.left :=
    A.range_projection_mem
  rw [Finset.sum_eq_single (ι := Set X.left) (Set.range A.projection)]
  · rw [dite_eq_left hAC]
    change FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := X) (Z := Y)
      (componentIdentityGenerator (X := X.left) X.hom _ hAC).cycle
      A.cycle = A.cycle
    rw [FiniteCorrespondence.incidenceTorPairing_cycle,
      A.incidenceTorCorrespondence_componentIdentity_left_of_range_eq k _ _ rfl]
  · intro C hC hCA
    have hC' : C ∈ irreducibleComponents X.left := by simpa using hC
    rw [dite_eq_left hC']
    change FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := X) (Z := Y)
      (componentIdentityGenerator (X := X.left) X.hom C hC').cycle A.cycle = 0
    rw [FiniteCorrespondence.incidenceTorPairing_cycle]
    exact A.incidenceTorCorrespondence_componentIdentity_left_of_ne k C hC' hCA
  · intro hnot
    exact (hnot (by simpa using hAC)).elim

end FiniteCorrespondenceGenerator

namespace FiniteCorrespondence
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] {X Y : SmoothSite (Spec (.of k))}

/-- The full actual diagonal is a right unit on all signed smooth correspondences. -/
theorem incidenceTorPairing_componentIdentity_right
    (α : FiniteCorrespondence X.hom Y.hom) :
    incidenceTorPairing k (X := X) (Y := Y) (Z := Y)
      α (componentIdentityCycle (X := Y.left) Y.hom) = α := by
  have heq : (incidenceTorPairing k (X := X) (Y := Y) (Z := Y)).flip
      (componentIdentityCycle (X := Y.left) Y.hom) =
      AddMonoidHom.id (FiniteCorrespondence X.hom Y.hom) := by
    apply Finsupp.addHom_ext
    intro A n
    have hsingle : Finsupp.single A n = n • A.cycle := by
      simp [FiniteCorrespondenceGenerator.cycle]
    rw [hsingle, map_zsmul]
    change n • incidenceTorPairing k (X := X) (Y := Y) (Z := Y)
      A.cycle (componentIdentityCycle (X := Y.left) Y.hom) = n • A.cycle
    rw [A.incidenceTorPairing_componentIdentity_right_cycle k]
  exact congrArg (fun F => F α) heq

/-- The full actual diagonal is a left unit on all signed smooth correspondences. -/
theorem incidenceTorPairing_componentIdentity_left
    (α : FiniteCorrespondence X.hom Y.hom) :
    incidenceTorPairing k (X := X) (Y := X) (Z := Y)
      (componentIdentityCycle (X := X.left) X.hom) α = α := by
  have heq : incidenceTorPairing k (X := X) (Y := X) (Z := Y)
      (componentIdentityCycle (X := X.left) X.hom) =
      AddMonoidHom.id (FiniteCorrespondence X.hom Y.hom) := by
    apply Finsupp.addHom_ext
    intro A n
    have hsingle : Finsupp.single A n = n • A.cycle := by
      simp [FiniteCorrespondenceGenerator.cycle]
    rw [hsingle, map_zsmul]
    change n • incidenceTorPairing k (X := X) (Y := X) (Z := Y)
      (componentIdentityCycle (X := X.left) X.hom) A.cycle = n • A.cycle
    rw [A.incidenceTorPairing_componentIdentity_left_cycle k]
  exact congrArg (fun F => F α) heq

end FiniteCorrespondence

end Motivic
