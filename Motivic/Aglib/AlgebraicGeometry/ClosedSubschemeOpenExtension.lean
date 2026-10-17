/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Extending an open in a closed subscheme

Removing the closed image of the unwanted part extends an open subscheme of a
closed subscheme to an open in the ambient scheme. The resulting square is
Cartesian as schemes, including nilpotents, not just on underlying supports.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- Extend a chosen open in a closed subscheme by removing its closed complement. -/
def closedSubschemeOpenExtension {T W : Scheme.{u}} (i : T ⟶ W)
    [IsClosedImmersion i] (V : T.Opens) : W.Opens :=
  ⟨(i '' (V : Set T)ᶜ)ᶜ, (i.isClosedEmbedding.isClosedMap _ V.isOpen.isClosed_compl).isOpen_compl⟩

@[simp]
theorem preimage_closedSubschemeOpenExtension {T W : Scheme.{u}} (i : T ⟶ W)
    [IsClosedImmersion i] (V : T.Opens) :
    i ⁻¹ᵁ closedSubschemeOpenExtension i V = V := by
  ext x
  change (i x ∉ i '' (V : Set T)ᶜ) ↔ x ∈ V
  constructor
  · intro h
    by_contra hx
    exact h ⟨x, hx, rfl⟩
  · rintro hx ⟨y, hy, he⟩
    exact hy (i.isClosedEmbedding.injective he ▸ hx)

/-- The whole chosen open, with its original scheme structure, is the inverse
image of its ambient extension. -/
theorem exists_open_extension_isPullback {Z T W : Scheme.{u}}
    (s : Z ⟶ T) [IsOpenImmersion s] (i : T ⟶ W) [IsClosedImmersion i] :
    ∃ (U : W.Opens) (j : Z ⟶ U.toScheme),
      j ≫ U.ι = s ≫ i ∧ IsPullback j s U.ι i := by
  let U := closedSubschemeOpenExtension i s.opensRange
  have h : Set.range (s ≫ i) ⊆ Set.range U.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    change i (s z) ∉ i '' (s.opensRange : Set T)ᶜ
    rintro ⟨t, ht, he⟩
    exact ht ⟨z, (i.isClosedEmbedding.injective he).symm⟩
  let j := IsOpenImmersion.lift U.ι (s ≫ i) h
  have hj : j ≫ U.ι = s ≫ i := IsOpenImmersion.lift_fac _ _ _
  refine ⟨U, j, hj, IsOpenImmersion.isPullback j s U.ι i hj.symm ?_⟩
  simpa only [Scheme.Opens.opensRange_ι] using preimage_closedSubschemeOpenExtension i s.opensRange

end AlgebraicGeometry.Scheme
