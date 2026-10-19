/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Support.FiniteShrinking
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Basic
public import Lean.Util.CollectAxioms

/-!
# Consumers of simultaneous finite-support shrinking

The consumers use actual signed finite correspondences, actual source
projections, negative multiplicities, and empty support after cancellation.
Smooth-site objects are allowed over any field; no support smoothness,
connectedness, perfectness, or Nisnevich lifting assumption is introduced.
-/

@[expose] public section

set_option linter.mathlibStandardSet true

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory AlgebraicGeometry Motivic

universe u

namespace MotivicTest.FiniteSupportShrinking

variable {S X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}

/-- Negative multiplicities retain the actual geometric generator in support. -/
theorem negative_generator_mem_support (Z : FiniteCorrespondenceGenerator f g) :
    Z ∈ (-Z.cycle).support := by
  simp [FiniteCorrespondenceGenerator.cycle]

/-- The containment conclusion applies to the negative generator itself. -/
example (Z : FiniteCorrespondenceGenerator f g)
    (Ω : ∀ T : (-Z.cycle).support, T.val.scheme.Opens) :
    Z.projection ⁻¹' ((-Z.cycle).supportShrinkingOpen Ω : Set X) ⊆
      Ω ⟨Z, negative_generator_mem_support Z⟩ :=
  (-Z.cycle).preimage_supportShrinkingOpen_subset Ω
    ⟨Z, negative_generator_mem_support Z⟩

/-- Empty support removes no points, even when its family is supplied separately. -/
example (Ω : ∀ Z : (0 : FiniteCorrespondence f g).support, Z.val.scheme.Opens) :
    (0 : FiniteCorrespondence f g).supportShrinkingOpen Ω = ⊤ := by
  simp

/-- Exact cancellation uses the actual signed support, not a union of presentations. -/
example (Z : FiniteCorrespondenceGenerator f g)
    (Ω : ∀ T : (Z.cycle - Z.cycle).support, T.val.scheme.Opens) :
    (Z.cycle - Z.cycle).supportShrinkingOpen Ω = ⊤ := by
  ext x
  simp [FiniteCorrespondence.supportShrinkingOpen]

/-- One bad point of a support fiber excludes its image from the common open. -/
example (α : FiniteCorrespondence f g)
    (Ω : ∀ Z : α.support, Z.val.scheme.Opens)
    (Z : α.support) (z : Z.val.scheme) (hz : z ∉ Ω Z) :
    Z.val.projection z ∉ α.supportShrinkingOpen Ω :=
  fun hx ↦ hz (α.preimage_supportShrinkingOpen_subset Ω Z hx)

/-- The intended consumer has precisely the actual smooth-site source maps,
with arbitrary signed multiplicities and arbitrary base field. -/
theorem smoothSite_signed_shrinking {k : Type u} [Field k]
    {X Y : SmoothSite (Spec (.of k))}
    (α : FiniteCorrespondence X.hom Y.hom) (x : X.left)
    (Ω : ∀ Z : α.support, Z.val.scheme.Opens)
    (hΩ : ∀ Z : α.support, Z.val.projection ⁻¹' {x} ⊆ Ω Z) :
    ∃ W : X.left.Opens, x ∈ W ∧
      ∀ Z : α.support, Z.val.projection ⁻¹' (W : Set X.left) ⊆ Ω Z :=
  α.exists_open_nhds_preimage_subset x Ω hΩ

open Lean in
run_cmd do
  let interfaces := #[
    ``FiniteCorrespondence.supportShrinkingOpen,
    ``FiniteCorrespondence.mem_supportShrinkingOpen_iff,
    ``FiniteCorrespondence.preimage_supportShrinkingOpen_subset,
    ``FiniteCorrespondence.supportShrinkingOpen_zero,
    ``FiniteCorrespondence.exists_open_nhds_preimage_subset,
    ``negative_generator_mem_support,
    ``smoothSite_signed_shrinking]
  for interface in interfaces do
    for dependency in ← collectAxioms interface do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "Interface {interface} depends on unsupported assumption {dependency}"
  logInfo "Finite-support shrinking uses only standard Lean logical foundations."

end MotivicTest.FiniteSupportShrinking
