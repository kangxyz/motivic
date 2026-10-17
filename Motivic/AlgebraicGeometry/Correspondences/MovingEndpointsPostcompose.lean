/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.AlgebraicGeometry.Correspondences.OneSidedMovingEndpoints
/-! # Moving into the original target after a base restriction -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
universe u
namespace Motivic.OneSidedMovingEndpoints

/-- Base restriction of the target does not change the requested original endpoint. -/
theorem HasMovingEndpoints.postcompose {k : Type u} [Field k]
    {S X V X₀ V₀ : SmoothSite (Spec (.of k))}
    {φ : S ⟶ X} {v : V ⟶ X} (h : HasMovingEndpoints φ v)
    (a : X ⟶ X₀) (b : V ⟶ V₀) (v₀ : V₀ ⟶ X₀) (hv : v ≫ a = b ≫ v₀) :
    HasMovingEndpoints (φ ≫ a) v₀ := by
  obtain ⟨β, α, h0, h1⟩ := h
  refine ⟨β ≫ (Cor.graphFunctor k).map b, α ≫ (Cor.graphFunctor k).map a, ?_, ?_⟩
  · rw [← Category.assoc, h0, ← Functor.map_comp]
  · rw [← Category.assoc, h1, Category.assoc, ← Functor.map_comp, hv,
      Functor.map_comp, Category.assoc]

end Motivic.OneSidedMovingEndpoints
