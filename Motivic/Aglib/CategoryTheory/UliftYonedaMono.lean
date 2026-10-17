/-
Copyright (c) 2026 Motivic cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# Monomorphisms under universe-lifted Yoneda

Postcomposition by a monomorphism is injective on each universe-lifted
representable. Consequently the actual functor `uliftYoneda` preserves
monomorphisms, without requiring limits in the source category.
-/

@[expose] public section

universe t v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- Postcomposition by a monomorphism is injective after lifting the hom universe. -/
theorem uliftYoneda_map_app_injective {X Y : C} (f : X ⟶ Y) [Mono f] (Z : Cᵒᵖ) :
    Function.Injective ((uliftYoneda.{t}.map f).app Z) := by
  intro a b h
  apply ULift.ext
  apply (cancel_mono f).1
  exact congrArg ULift.down h

/-- Universe-lifted Yoneda preserves monomorphisms objectwise. -/
instance uliftYoneda_preservesMonomorphisms :
    (uliftYoneda.{t} (C := C)).PreservesMonomorphisms where
  preserves f _ := by
    have : ∀ Z, Mono ((uliftYoneda.{t}.map f).app Z) := fun Z ↦
      (mono_iff_injective _).2 (uliftYoneda_map_app_injective f Z)
    exact NatTrans.mono_of_mono_app _

end CategoryTheory
