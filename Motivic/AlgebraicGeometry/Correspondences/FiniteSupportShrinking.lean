/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Generators

/-!
# Simultaneous open shrinking for finite correspondence supports

For every generator in the actual finite support of a signed correspondence,
choose an open subset of its integral support scheme. The complement of the
union of the closed images of their complements is an open subset of the
source, whose inverse image lies in every chosen open. It contains a source
point precisely when the chosen opens contain all the corresponding fibers.

Only finiteness of the actual source projections and of the cycle support is
used. No smoothness or perfectness assumption is needed. This is a topological
shrinking lemma, not a Nisnevich cover-lifting or transfer-sheafification theorem.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondence

variable {S X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}

/-- Remove the closed images of the complements of the chosen support opens. -/
noncomputable def supportShrinkingOpen (α : FiniteCorrespondence f g)
    (Ω : ∀ Z : α.support, Z.val.scheme.Opens) : X.Opens :=
  ⟨(⋃ Z : α.support, Z.val.projection '' (Ω Z : Set Z.val.scheme)ᶜ)ᶜ,
    (isClosed_iUnion_of_finite fun Z ↦
      Z.val.projection.isClosedMap _ (Ω Z).isOpen.isClosed_compl).isOpen_compl⟩

/-- The canonical shrinking contains exactly the points whose full fibers lie
in the chosen support opens. -/
theorem mem_supportShrinkingOpen_iff (α : FiniteCorrespondence f g)
    (Ω : ∀ Z : α.support, Z.val.scheme.Opens) (x : X) :
    x ∈ α.supportShrinkingOpen Ω ↔
      ∀ Z : α.support, Z.val.projection ⁻¹' {x} ⊆ Ω Z := by
  change (x ∉ ⋃ Z : α.support, Z.val.projection '' (Ω Z : Set Z.val.scheme)ᶜ) ↔ _
  constructor
  · intro hx Z z hz
    by_contra hzΩ
    exact hx (Set.mem_iUnion_of_mem Z ⟨z, hzΩ, Set.mem_singleton_iff.mp hz⟩)
  · intro hΩ hx
    rcases Set.mem_iUnion.mp hx with ⟨Z, z, hz, hzx⟩
    exact hz (hΩ Z (Set.mem_singleton_iff.mpr hzx))

/-- Every actual source projection above the common shrinking lands in its
chosen open, simultaneously across the full signed support. -/
theorem preimage_supportShrinkingOpen_subset (α : FiniteCorrespondence f g)
    (Ω : ∀ Z : α.support, Z.val.scheme.Opens) (Z : α.support) :
    Z.val.projection ⁻¹' (α.supportShrinkingOpen Ω : Set X) ⊆ Ω Z := by
  intro z hz
  by_contra hzΩ
  change Z.val.projection z ∉
    ⋃ W : α.support, W.val.projection '' (Ω W : Set W.val.scheme)ᶜ at hz
  exact hz (Set.mem_iUnion_of_mem Z ⟨z, hzΩ, rfl⟩)

/-- An empty signed support imposes no restriction on the source open. -/
@[simp]
theorem supportShrinkingOpen_zero
    (Ω : ∀ Z : (0 : FiniteCorrespondence f g).support, Z.val.scheme.Opens) :
    (0 : FiniteCorrespondence f g).supportShrinkingOpen Ω = ⊤ := by
  ext x
  simp [supportShrinkingOpen]

/-- Opens containing every support fiber above a point admit one common source
neighborhood, with no hypotheses on the signs of the multiplicities. -/
theorem exists_open_nhds_preimage_subset (α : FiniteCorrespondence f g) (x : X)
    (Ω : ∀ Z : α.support, Z.val.scheme.Opens)
    (hΩ : ∀ Z : α.support, Z.val.projection ⁻¹' {x} ⊆ Ω Z) :
    ∃ W : X.Opens, x ∈ W ∧
      ∀ Z : α.support, Z.val.projection ⁻¹' (W : Set X) ⊆ Ω Z :=
  ⟨α.supportShrinkingOpen Ω, (α.mem_supportShrinkingOpen_iff Ω x).mpr hΩ,
    α.preimage_supportShrinkingOpen_subset Ω⟩

end Motivic.FiniteCorrespondence
