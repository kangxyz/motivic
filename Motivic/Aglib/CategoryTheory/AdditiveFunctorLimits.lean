/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Limits of additive functors

Additivity in source arrows is preserved under ordinary functor-category
limits. Consequently the full subcategory of additive functors inherits
limits whenever the target category has them; its inclusion creates them.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  {J : Type u₃} [Category.{v₃} J] [HasLimitsOfShape J D]

/-- A limit of additive functors is additive in the source arrows. -/
theorem Functor.additive_of_isLimit {F : J ⥤ C ⥤ D} {c : Cone F}
    (hc : IsLimit c) (hF : ∀ j, (F.obj j).Additive) : c.pt.Additive where
  map_add {X Y f g} := by
    apply (isLimitOfPreserves ((evaluation C D).obj Y) hc).hom_ext
    intro j
    let := hF j
    change c.pt.map (f + g) ≫ (c.π.app j).app Y =
      (c.pt.map f + c.pt.map g) ≫ (c.π.app j).app Y
    rw [NatTrans.naturality, Functor.map_add, Preadditive.add_comp,
      Preadditive.comp_add, NatTrans.naturality, NatTrans.naturality]

instance additiveFunctor_isClosedUnderLimitsOfShape :
    (additiveFunctor C D).IsClosedUnderLimitsOfShape J where
  limitsOfShape_le := by
    rintro P ⟨h⟩
    exact Functor.additive_of_isLimit h.isLimit h.prop_diag_obj

end CategoryTheory
