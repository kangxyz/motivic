/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.Sets.Opens

/-! # Closed-point neighborhoods form a genuine open cover in a Jacobson space -/
@[expose] public section
open TopologicalSpace
universe u v
namespace TopologicalSpace.Opens
variable {X : Type u} [TopologicalSpace X] [JacobsonSpace X]

/-- An open containing all closed points is the entire Jacobson space. -/
theorem eq_top_of_closedPoints_subset (U : Opens X) (h : closedPoints X ⊆ U) : U = ⊤ := by
  apply SetLike.coe_injective
  apply Set.eq_univ_of_forall
  intro x
  by_contra hx
  obtain ⟨y, hy, hc⟩ := nonempty_inter_closedPoints
    (Z := (U : Set X)ᶜ) ⟨x, hx⟩ U.isOpen.isClosed_compl.isLocallyClosed
  exact hy (h hc)

/-- Neighborhoods chosen at every closed point cover every point, not merely the
closed-point subspace. This does not assert any presheaf gluing or separatedness. -/
theorem iSup_eq_top_of_closedPoint_neighborhoods {ι : Type v} (U : ι → Opens X)
    (h : ∀ x : X, IsClosed ({x} : Set X) → ∃ i, x ∈ U i) : (⨆ i, U i) = ⊤ := by
  apply eq_top_of_closedPoints_subset
  intro x hx
  obtain ⟨i, hi⟩ := h x hx
  exact (le_iSup U i) hi

end TopologicalSpace.Opens
