/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.FiniteEtaleNeighborhoodIso
public import Mathlib.AlgebraicGeometry.Artinian

/-!
# Étale isomorphisms over reduced discrete schemes

The residue-field maps of a reduced discrete scheme form an actual open cover.
An étale map with one residue-field-preserving point in each fiber is therefore
an isomorphism of schemes. This criterion supplies the scheme-level conclusion
needed over a finite reduced complement, rather than only a statement about points.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- Every stalk of a reduced discrete scheme is a field. -/
theorem isField_stalk_of_discrete {X : Scheme.{u}} [IsReduced X] [DiscreteTopology X] (x : X) :
    IsField (X.presheaf.stalk x) := by
  apply isField_stalk_of_closure_mem_irreducibleComponents
  have h : irreducibleComponent x = {x} := by
    apply Set.Subset.antisymm
    · intro y hy
      exact (isIrreducible_irreducibleComponent.isPreirreducible.subsingleton hy
        mem_irreducibleComponent)
    · exact Set.singleton_subset_iff.mpr mem_irreducibleComponent
  rw [closure_singleton, ← h]
  exact irreducibleComponent_mem_irreducibleComponents x

/-- The literal residue-field inclusion is open over a reduced discrete scheme. -/
instance isOpenImmersion_fromSpecResidueField_of_discrete
    (X : Scheme.{u}) [IsReduced X] [DiscreteTopology X] (x : X) :
    IsOpenImmersion (X.fromSpecResidueField x) := by
  apply IsOpenImmersion.iff_isIso_stalkMap.mpr
  refine ⟨.of_continuous_injective_isOpenMap (X.fromSpecResidueField x).continuous
    (X.fromSpecResidueField x).isEmbedding.injective (fun _ _ ↦ isOpen_discrete _), ?_⟩
  intro y
  let : Field (X.presheaf.stalk (X.fromSpecResidueField x y)) :=
    (isField_stalk_of_discrete _).toField
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact ⟨(X.fromSpecResidueField x).stalkMap y |>.hom.injective,
    (X.fromSpecResidueField x).stalkMap_surjective y⟩

/-- Residue-field inclusions give an actual scheme open cover. -/
def residueFieldOpenCover (X : Scheme.{u}) [IsReduced X] [DiscreteTopology X] : X.OpenCover :=
  Cover.mkOfCovers X (fun x ↦ Spec (X.residueField x)) X.fromSpecResidueField
    (fun x ↦ ⟨x, IsLocalRing.closedPoint _, X.fromSpecResidueField_apply _ _⟩)


/-- Singleton residue-field-preserving fibers imply an actual étale
isomorphism over a reduced discrete scheme. -/
theorem isIso_of_etale_singleton_residue_fibers
    {Y X : Scheme.{u}} (p : Y ⟶ X) [Etale p] [IsReduced X] [DiscreteTopology X]
    (h : ∀ x : X, ∃ y : Y, p y = x ∧ IsIso (p.residueFieldMap y) ∧
      ∀ y' : Y, p y' = x → y' = y) : IsIso p := by
  apply IsZariskiLocalAtTarget.of_openCover (residueFieldOpenCover X)
  intro x
  obtain ⟨y, rfl, hy, huniq⟩ := h x
  exact p.isIso_fiberToSpecResidueField_of_singleton y huniq

end AlgebraicGeometry.Scheme
