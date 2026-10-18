/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.PresheavesWithTransfers.GraphRestriction

/-! # Restricting signed corrections along actual refinement squares

This is sectionwise functoriality on the unchanged presheaf with transfers.
It does not construct geometric refinements or assume a lifting family.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe v u

namespace Motivic.PresheafWithTransfers

/-- Restrict both corrections along literal commuting refinement squares. -/
theorem restriction_difference_refinement
    {k : Type u} [Field k] (P : PresheafWithTransfers.{v} k)
    {O T A D O' T' A' : SmoothSite (Spec (.of k))}
    (β : O ⟶ T) (α : O ⟶ A) (φ : O ⟶ D)
    (β' : O' ⟶ T') (α' : O' ⟶ A') (φ' : O' ⟶ D)
    (q : O ⟶ O') (t : T ⟶ T') (e : A ⟶ A')
    (hβ : q ≫ β' = β ≫ t) (hα : q ≫ α' = α ≫ e) (hφ : q ≫ φ' = φ)
    (s : sections P (Cor.mk D)) (a : sections P (Cor.mk T'))
    (c : sections P (Cor.mk A'))
    (h : transfer P ((Cor.graphFunctor k).map β') a -
      transfer P ((Cor.graphFunctor k).map α') c =
      transfer P ((Cor.graphFunctor k).map φ') s) :
    transfer P ((Cor.graphFunctor k).map β)
        (transfer P ((Cor.graphFunctor k).map t) a) -
      transfer P ((Cor.graphFunctor k).map α)
        (transfer P ((Cor.graphFunctor k).map e) c) =
      transfer P ((Cor.graphFunctor k).map φ) s := by
  have ht := congrArg (transfer P ((Cor.graphFunctor k).map q)) h
  simp only [map_sub] at ht
  have hc {U V Z : SmoothSite (Spec (.of k))} (f : U ⟶ V) (g : V ⟶ Z)
      (x : sections P (Cor.mk Z)) :
      transfer P ((Cor.graphFunctor k).map f)
          (transfer P ((Cor.graphFunctor k).map g) x) =
        transfer P ((Cor.graphFunctor k).map (f ≫ g)) x := by
    rw [Functor.map_comp, transfer_comp, ConcreteCategory.comp_apply]
  rw [hc, hc, hc, hβ, hα, hφ, ← hc, ← hc] at ht
  exact ht

end Motivic.PresheafWithTransfers
