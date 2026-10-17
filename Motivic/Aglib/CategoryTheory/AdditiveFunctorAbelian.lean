/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.CategoryTheory.AdditiveFunctorLimits
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages

/-!
# Colimits and abelianness of additive functors

Additivity in source arrows is closed under colimits as well as limits.
The inclusion of additive functors therefore preserves kernels and cokernels.
The ordinary functor-category coimage-image comparison proves that the actual
category of additive functors into an abelian category is abelian.
-/

@[expose] public noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  {D : Type u₂} [Category.{v₂} D]

section Colimits

variable [Preadditive D] {J : Type u₃} [Category.{v₃} J]

/-- A colimit of additive functors remains additive in source arrows. -/
theorem Functor.additive_of_isColimit [HasColimitsOfShape J D]
    {F : J ⥤ C ⥤ D} {c : Cocone F}
    (hc : IsColimit c) (hF : ∀ j, (F.obj j).Additive) : c.pt.Additive where
  map_add {X Y f g} := by
    apply (isColimitOfPreserves ((evaluation C D).obj X) hc).hom_ext
    intro j
    let := hF j
    change (c.ι.app j).app X ≫ c.pt.map (f + g) =
      (c.ι.app j).app X ≫ (c.pt.map f + c.pt.map g)
    have hn (a : X ⟶ Y) : (F.obj j).map a ≫ (c.ι.app j).app Y =
        (c.ι.app j).app X ≫ c.pt.map a := (c.ι.app j).naturality a
    rw [← hn (f + g), Functor.map_add, Preadditive.add_comp,
      Preadditive.comp_add, hn f, hn g]

instance additiveFunctor_isClosedUnderColimitsOfShape [HasColimitsOfShape J D] :
    (additiveFunctor C D).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro P ⟨h⟩
    exact Functor.additive_of_isColimit h.isColimit h.prop_diag_obj

end Colimits

variable [Abelian D]

instance AdditiveFunctor.hasFiniteProducts : HasFiniteProducts (C ⥤+ D) :=
  ⟨fun _ => inferInstance⟩

instance AdditiveFunctor.forget_preservesFiniteLimits :
    PreservesFiniteLimits (AdditiveFunctor.forget C D) :=
  ⟨fun _ _ _ => inferInstance⟩

instance AdditiveFunctor.forget_preservesFiniteColimits :
    PreservesFiniteColimits (AdditiveFunctor.forget C D) :=
  ⟨fun _ _ _ => inferInstance⟩

/-- The coimage-image comparison is detected by the inclusion into all functors. -/
instance AdditiveFunctor.isIso_coimageImageComparison {F G : C ⥤+ D} (η : F ⟶ G) :
    IsIso (Abelian.coimageImageComparison η) := by
  let U := AdditiveFunctor.forget C D
  have : IsIso (U.map (Abelian.coimageImageComparison η)) := by
    rw [Arrow.isIso_iff_isIso_of_isIso
      (Abelian.PreservesCoimageImageComparison.iso U η).hom]
    infer_instance
  exact isIso_of_reflects_iso _ U

/-- Additive functors into an abelian category form an abelian category. -/
instance AdditiveFunctor.abelian : Abelian (C ⥤+ D) :=
  Abelian.ofCoimageImageComparisonIsIso

end CategoryTheory
