/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ClosedCentersFiniteSupport

/-!
# Isolating one branch over finitely many closed centers

For a quasi-compact, locally quasi-finite morphism, the inverse image of a finite
set of closed points is finite and consists of closed points. Removing every
one of these points except a designated point gives an open neighborhood
meeting that inverse image in at most the designated point. An affine open
inside this neighborhood gives the same control with an actual open immersion.

Only the selected finite set of fibers is used. The source and target need not
be reduced, Jacobson, or schemes over a field.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {U X : Scheme.{u}} (f : U ⟶ X) [LocallyQuasiFinite f] [QuasiCompact f]
  (T : Set X) (hT : T.Finite) (hclosed : ∀ x ∈ T, IsClosed ({x} : Set X)) (u : U)

include hT hclosed

/-- An open neighborhood isolates a designated point from all the other points
above a given finite set of closed centers. -/
theorem exists_open_isolating_finite_closed_fibers :
    ∃ W : U.Opens, u ∈ W ∧ ∀ v ∈ W, f v ∈ T → v = u := by
  let B : Set U := f ⁻¹' T \ {u}
  have hB : B.Finite := (f.finite_preimage hT).subset Set.sdiff_subset
  have hBclosed : IsClosed B := by
    have h := hB.isClosed_biUnion fun v hv ↦
      f.isClosed_singleton_of_isClosed_singleton_image v (hclosed (f v) hv.1)
    simpa only [Set.biUnion_of_singleton] using h
  refine ⟨⟨Bᶜ, hBclosed.isOpen_compl⟩, ?_, ?_⟩
  · simp [B]
  · intro v hv hfv
    by_contra hne
    exact hv ⟨hfv, hne⟩

/-- The isolating neighborhood can be chosen affine, with its actual open immersion. -/
theorem exists_affine_isolating_finite_closed_fibers :
    ∃ (R : CommRingCat.{u}) (j : Spec R ⟶ U), IsOpenImmersion j ∧
      u ∈ Set.range j ∧ ∀ v : Spec R, f (j v) ∈ T → j v = u := by
  obtain ⟨W, hu, hW⟩ := f.exists_open_isolating_finite_closed_fibers T hT hclosed u
  obtain ⟨R, j, hj, hu, hjW⟩ := Scheme.exists_affine_mem_range_and_range_subset hu
  exact ⟨R, j, hj, hu, fun v hv ↦ hW (j v) (hjW ⟨v, rfl⟩) hv⟩

end AlgebraicGeometry.Scheme.Hom
