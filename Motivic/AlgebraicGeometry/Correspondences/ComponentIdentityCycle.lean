/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.ComponentGraphs
public import Motivic.AlgebraicGeometry.Correspondences.CompositionSupportGraphs
public import Motivic.AlgebraicGeometry.SmoothSiteNormal
public import Motivic.AlgebraicGeometry.SmoothSiteReduced

/-!
# Genuine componentwise identity cycles

The graph cycle is transported along its actual structural equality over the
base. In particular the identity cycle is defined for every reduced Noetherian
separated scheme, including disconnected and empty schemes. Its components
are genuine graph generators, each with coefficient one. On smooth objects,
their source projections are open immersions, proved from the actual clopen
component geometry. No unit law for a pairing is assumed here.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic

section GraphTransport

variable {S X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
  [IsNoetherian X] [IsReduced X] [IsSeparated g]

/-- A genuine component graph transported by its actual structural equality. -/
noncomputable def componentGraphGeneratorOver (φ : X ⟶ Y) (w : φ ≫ g = f)
    (C : Set X) (hC : C ∈ irreducibleComponents X) : FiniteCorrespondenceGenerator f g :=
  w ▸ componentGraphGenerator φ g C hC

/-- The whole component graph cycle transported by its structural equality. -/
noncomputable def componentGraphCycleOver (φ : X ⟶ Y) (w : φ ≫ g = f) :
    FiniteCorrespondence f g := w ▸ componentGraphCycle φ g

/-- Every actual component still has coefficient one after the structural transport. -/
@[simp]
theorem componentGraphCycleOver_coefficient (φ : X ⟶ Y) (w : φ ≫ g = f)
    (C : Set X) (hC : C ∈ irreducibleComponents X) :
    componentGraphCycleOver φ w (componentGraphGeneratorOver φ w C hC) = 1 := by
  subst f
  exact componentGraphCycle_coefficient φ g C hC

open Classical in
/-- The transported cycle is the finite sum of the transported geometric components. -/
theorem componentGraphCycleOver_eq_sum (φ : X ⟶ Y) (w : φ ≫ g = f) :
    componentGraphCycleOver φ w =
      ∑ C ∈ TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.toFinset,
        if hC : C ∈ irreducibleComponents X then
          (componentGraphGeneratorOver φ w C hC).cycle else 0 := by
  subst f
  rfl

/-- The two actual component graph projections are related by the original map. -/
@[reassoc]
theorem componentGraphGeneratorOver_projection_target (φ : X ⟶ Y) (w : φ ≫ g = f)
    (C : Set X) (hC : C ∈ irreducibleComponents X) :
    (componentGraphGeneratorOver φ w C hC).projection ≫ φ =
      (componentGraphGeneratorOver φ w C hC).targetProjection := by
  subst f
  have : IsIso (componentGraph φ g C hC).toImage :=
    IsClosedImmersion.instIsIsoSchemeToImage _
  apply (cancel_epi (componentGraph φ g C hC).toImage).mp
  simp [componentGraphGeneratorOver, componentGraphGenerator,
    FiniteCorrespondenceGenerator.projection, FiniteCorrespondenceGenerator.targetProjection,
    FiniteCorrespondenceGenerator.inclusion, componentGraphIdeal,
    correspondenceProjection, componentGraph]

/-- Integral sources recover their actual single graph generator cycle. -/
@[simp]
theorem componentGraphCycleOver_eq_graphGeneratorOver_cycle [IsIntegral X]
    (φ : X ⟶ Y) (w : φ ≫ g = f) :
    componentGraphCycleOver φ w = (graphGeneratorOver φ w).cycle := by
  subst f
  exact componentGraphCycle_eq_graphCycle φ g

end GraphTransport

section Identity

variable {S X : Scheme.{u}} (f : X ⟶ S)
  [IsNoetherian X] [IsReduced X] [IsSeparated f]

/-- The genuine diagonal component generator on a possibly disconnected scheme. -/
noncomputable def componentIdentityGenerator (C : Set X)
    (hC : C ∈ irreducibleComponents X) : FiniteCorrespondenceGenerator f f :=
  componentGraphGeneratorOver (𝟙 X) (Category.id_comp f) C hC

/-- The full identity candidate is the actual finite sum of diagonal components. -/
noncomputable def componentIdentityCycle : FiniteCorrespondence f f :=
  componentGraphCycleOver (𝟙 X) (Category.id_comp f)

/-- Each actual diagonal component has coefficient exactly one. -/
@[simp]
theorem componentIdentityCycle_coefficient (C : Set X)
    (hC : C ∈ irreducibleComponents X) :
    componentIdentityCycle f (componentIdentityGenerator f C hC) = 1 :=
  componentGraphCycleOver_coefficient (𝟙 X) (Category.id_comp f) C hC

/-- Both projections of an actual diagonal component coincide. -/
@[simp]
theorem componentIdentityGenerator_targetProjection (C : Set X)
    (hC : C ∈ irreducibleComponents X) :
    (componentIdentityGenerator f C hC).targetProjection =
      (componentIdentityGenerator f C hC).projection := by
  simpa only [componentIdentityGenerator, Category.comp_id] using
    (componentGraphGeneratorOver_projection_target (𝟙 X) (Category.id_comp f) C hC).symm

/-- The full diagonal specializes to the original identity generator on integral schemes. -/
@[simp]
theorem componentIdentityCycle_eq_identityGenerator_cycle [IsIntegral X] :
    componentIdentityCycle f = (identityGenerator f).cycle :=
  componentGraphCycleOver_eq_graphGeneratorOver_cycle (𝟙 X) (Category.id_comp f)

/-- The actual identity cycle of the empty scheme is zero. -/
@[simp]
theorem componentIdentityCycle_eq_zero_of_isEmpty [IsEmpty X] :
    componentIdentityCycle f = 0 := by
  ext A
  exact isEmptyElim (A.projection (Classical.arbitrary A.scheme))

end Identity

section OpenComponents

variable {X : Scheme.{u}} [IsNoetherian X]

/-- Disjoint irreducible components identify the defining component open with its component. -/
theorem coe_irreducibleComponentOpen_of_pairwiseDisjoint
    (hX : (irreducibleComponents X).PairwiseDisjoint id)
    (C : Set X) (hC : C ∈ irreducibleComponents X) :
    (X.irreducibleComponentOpen C : Set X) = C := by
  ext x
  change x ∉ ⋃₀ (irreducibleComponents X \ {C}) ↔ x ∈ C
  constructor
  · intro hx
    by_contra hxC
    apply hx
    refine ⟨irreducibleComponent x,
      ⟨irreducibleComponent_mem_irreducibleComponents x, ?_⟩, mem_irreducibleComponent⟩
    simpa only [Set.mem_singleton_iff] using
      fun h : irreducibleComponent x = C ↦ hxC (h ▸ mem_irreducibleComponent)
  · intro hxC
    rintro ⟨D, ⟨hD, hDC⟩, hxD⟩
    have hne : C ≠ D := fun h ↦ hDC (Set.mem_singleton_iff.mpr h.symm)
    exact Set.disjoint_left.mp (hX hC hD hne) hxC hxD

/-- The genuine closed component inclusion is also open when the components are disjoint. -/
theorem isOpenImmersion_irreducibleComponentι_of_pairwiseDisjoint
    (hX : (irreducibleComponents X).PairwiseDisjoint id)
    (C : Set X) (hC : C ∈ irreducibleComponents X) :
    IsOpenImmersion (X.irreducibleComponentι C hC) := by
  have hclosed : IsClosed (Set.range (X.irreducibleComponentOpen C).ι) := by
    rw [(X.irreducibleComponentOpen C).range_ι,
      coe_irreducibleComponentOpen_of_pairwiseDisjoint hX C hC]
    exact isClosed_of_mem_irreducibleComponents C hC
  have : IsClosedImmersion (X.irreducibleComponentOpen C).ι :=
    IsClosedImmersion.of_isPreimmersion _ hclosed
  have : IsIso (X.irreducibleComponentOpen C).ι.toImage :=
    IsClosedImmersion.instIsIsoSchemeToImage _
  change IsOpenImmersion (X.irreducibleComponentIdeal C hC).subschemeι
  rw [Scheme.irreducibleComponentIdeal_def]
  have heq : (X.irreducibleComponentOpen C).ι.imageι =
      inv (X.irreducibleComponentOpen C).ι.toImage ≫ (X.irreducibleComponentOpen C).ι := by
    apply (cancel_epi (X.irreducibleComponentOpen C).ι.toImage).mp
    simp
  rw [show (X.irreducibleComponentOpen C).ι.ker.subschemeι =
    (X.irreducibleComponentOpen C).ι.imageι from rfl, heq]
  infer_instance

end OpenComponents

section OpenGraphs

variable {S X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
  [IsNoetherian X] [IsReduced X] [IsSeparated g]

/-- Actual component graphs over disjoint components have open source projection. -/
theorem componentGraphGeneratorOver_projection_isOpenImmersion
    (hX : (irreducibleComponents X).PairwiseDisjoint id)
    (φ : X ⟶ Y) (w : φ ≫ g = f)
    (C : Set X) (hC : C ∈ irreducibleComponents X) :
    IsOpenImmersion (componentGraphGeneratorOver φ w C hC).projection := by
  subst f
  have : IsOpenImmersion (X.irreducibleComponentι C hC) :=
    isOpenImmersion_irreducibleComponentι_of_pairwiseDisjoint hX C hC
  have : IsIso (componentGraph φ g C hC).toImage :=
    IsClosedImmersion.instIsIsoSchemeToImage _
  change IsOpenImmersion (correspondenceProjection (φ ≫ g) g (componentGraphIdeal φ g C hC))
  have heq : correspondenceProjection (φ ≫ g) g (componentGraphIdeal φ g C hC) =
      inv (componentGraph φ g C hC).toImage ≫ X.irreducibleComponentι C hC := by
    apply (cancel_epi (componentGraph φ g C hC).toImage).mp
    simp
  rw [heq]
  have : IsIso (inv (componentGraph φ g C hC).toImage) :=
    (asIso (componentGraph φ g C hC).toImage).symm.isIso_hom
  exact MorphismProperty.IsStableUnderComposition.comp_mem
    (P := @IsOpenImmersion) (inv (componentGraph φ g C hC).toImage)
    (X.irreducibleComponentι C hC)
    (IsOpenImmersion.of_isIso _) inferInstance

end OpenGraphs

namespace SmoothSite

variable (k : Type u) [Field k] (X : SmoothSite (Spec (.of k)))

local instance : IsNoetherian ((𝟭 Scheme).obj X.left) :=
  inferInstanceAs (IsNoetherian X.left)

local instance : IsReduced ((𝟭 Scheme).obj X.left) :=
  inferInstanceAs (IsReduced X.left)

/-- Every actual smooth diagonal component has open source projection. -/
instance componentIdentityGenerator_projection_isOpenImmersion
    (C : Set X.left) (hC : C ∈ irreducibleComponents X.left) :
    IsOpenImmersion (componentIdentityGenerator X.hom C hC).projection :=
  componentGraphGeneratorOver_projection_isOpenImmersion
    (pairwiseDisjoint_irreducibleComponents k X) (𝟙 _) (Category.id_comp X.hom) C hC

/-- Every actual smooth diagonal component has open target projection as well. -/
instance componentIdentityGenerator_targetProjection_isOpenImmersion
    (C : Set X.left) (hC : C ∈ irreducibleComponents X.left) :
    IsOpenImmersion (componentIdentityGenerator X.hom C hC).targetProjection := by
  rw [componentIdentityGenerator_targetProjection]
  infer_instance

end SmoothSite

end Motivic
