/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Finite ambient affine covers of actual closed inverse-image opens

Every affine open in a closed subscheme is covered by finitely many inverse
images of ambient affine opens, all lying inside the original open. Applying
this to the whole affine inverse image under a finite morphism retains every
source branch. No single ambient rectangle is presumed to contain that fiber.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Motivic.ClosedAffineCover

variable {X P : Scheme.{u}} (j : X ⟶ P) [IsClosedImmersion j]

/-- Every actual source-open neighborhood contains a closed inverse image of
an ambient affine neighborhood of the same point. -/
theorem exists_ambient_affine_neighborhood (V : X.Opens) {x : X} (hx : x ∈ V) :
    ∃ U : P.affineOpens, x ∈ j ⁻¹ᵁ U ∧ j ⁻¹ᵁ U ≤ V := by
  obtain ⟨O, hO, hpre⟩ := j.isClosedEmbedding.isInducing.isOpen_iff.mp V.isOpen
  have hxO : j x ∈ O := by
    change x ∈ j ⁻¹' O
    rw [hpre]
    exact hx
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUO⟩ :=
    P.isBasis_affineOpens.exists_subset_of_mem_open hxO hO
  refine ⟨⟨U, hU⟩, hxU, ?_⟩
  intro y hy
  change y ∈ (V : Set X)
  rw [← hpre]
  exact hUO hy

/-- The entire affine source open admits a finite ambient affine cover subordinate
to that open; the finite family is derived from actual quasi-compactness. -/
theorem exists_finite_ambient_affine_cover (V : X.affineOpens) :
    ∃ s : Finset P.affineOpens,
      (∀ U ∈ s, j ⁻¹ᵁ U ≤ V.1) ∧ (⨆ U ∈ s, j ⁻¹ᵁ U) = V.1 := by
  classical
  let I := {U : P.affineOpens // j ⁻¹ᵁ U ≤ V.1}
  have hcover : (V.1 : Set X) ⊆ ⋃ U : I, ((j ⁻¹ᵁ U.1) : Set X) := by
    intro x hx
    obtain ⟨U, hxU, hUV⟩ := exists_ambient_affine_neighborhood j V.1 hx
    exact Set.mem_iUnion.mpr ⟨⟨U, hUV⟩, hxU⟩
  obtain ⟨s, hs⟩ := V.2.isCompact.elim_finite_subcover
    (fun U : I => ((j ⁻¹ᵁ U.1) : Set X)) (fun U => (j ⁻¹ᵁ U.1).isOpen) hcover
  let t : Finset P.affineOpens := s.image Subtype.val
  have ht : ∀ U ∈ t, j ⁻¹ᵁ U ≤ V.1 := by
    intro U hU
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hU
    exact a.property
  refine ⟨t, ht, le_antisymm (iSup_le fun U => iSup_le fun hU => ht U hU) ?_⟩
  intro x hx
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (hs hx)
  obtain ⟨ha, hxa⟩ := Set.mem_iUnion.mp ha
  have hin : j ⁻¹ᵁ a.val ≤ ⨆ U ∈ t, j ⁻¹ᵁ U :=
    le_iSup_of_le a.val
      (le_iSup_of_le (Finset.mem_image.mpr ⟨a, ha, rfl⟩) le_rfl)
  exact hin hxa

/-- Every member of the ambient cover has a genuine affine closed inverse image. -/
theorem preimage_isAffineOpen (U : P.affineOpens) : IsAffineOpen (j ⁻¹ᵁ U) :=
  U.2.preimage j

/-- A finite morphism gives a finite ambient affine cover of its whole target-open
inverse image, rather than of only a selected point or branch. -/
theorem finiteMap_exists_whole_preimage_cover {Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (U : Y.affineOpens) :
    ∃ s : Finset P.affineOpens,
      (∀ V ∈ s, j ⁻¹ᵁ V ≤ f ⁻¹ᵁ U) ∧ (⨆ V ∈ s, j ⁻¹ᵁ V) = f ⁻¹ᵁ U :=
  exists_finite_ambient_affine_cover j ⟨f ⁻¹ᵁ U, U.2.preimage f⟩

end Motivic.ClosedAffineCover
