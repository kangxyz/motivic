/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.CurveOpenShrinking

/-! # Curve shrinking through the original open immersion

This version retains an arbitrary original open immersion, in particular the
literal open leg of a categorical pullback, rather than replacing its source
by a chosen isomorphic open subscheme.
-/

@[expose] public noncomputable section

open TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- Remove the complete finite closed support through the original open
immersion. The ambient open retains every point outside its original range,
and its literal inverse-image open is exactly the prescribed smaller open. -/
theorem exists_open_shrinking_of_openImmersion
    {W V : Scheme.{u}} [IsNoetherian W] [JacobsonSpace V]
    (i : W ⟶ V) [IsOpenImmersion i] (O : W.Opens)
    (hgeneric : genericPoints W ⊆ (O : Set W))
    (hdim : topologicalKrullDim W ≤ 1) :
    ∃ T : V.Opens, (Set.range i)ᶜ ⊆ (T : Set V) ∧
      i ⁻¹ᵁ T = O ∧ ((T : Set V)ᶜ).Finite := by
  obtain ⟨hfinite, hclosed⟩ :=
    finite_closed_complement_of_genericPoints_subset O hgeneric hdim
  let E : Set V := i '' (O : Set W)ᶜ
  have hEfinite : E.Finite := hfinite.image i
  have hEclosed : IsClosed E := by
    rw [show E = ⋃ x ∈ E, ({x} : Set V) by simp]
    apply hEfinite.isClosed_biUnion
    rintro x ⟨y, hy, rfl⟩
    exact i.closePoints_subset_preimage_closedPoints (hclosed y hy)
  let T : V.Opens := ⟨Eᶜ, hEclosed.isOpen_compl⟩
  refine ⟨T, ?_, ?_, ?_⟩
  · rintro x hx ⟨y, _, rfl⟩
    exact hx ⟨y, rfl⟩
  · ext x
    change i x ∉ E ↔ x ∈ O
    simp only [E, Set.mem_image, Set.mem_compl_iff]
    constructor
    · intro hx
      by_contra hn
      exact hx ⟨x, hn, rfl⟩
    · rintro hx ⟨y, hy, he⟩
      exact hy (i.isOpenEmbedding.injective he ▸ hx)
  · simpa only [T, Opens.coe_mk, compl_compl] using hEfinite

end AlgebraicGeometry.Scheme
