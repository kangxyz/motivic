/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Detecting colimit preservation through a reflection

A functor out of a reflective subcategory preserves colimits if its composite
with the reflector does. The proof uses a colimit in the ambient category and
the actual reflection isomorphism, without assuming that the inclusion
preserves colimits.
-/

@[expose] public noncomputable section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]
  {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]
  {J : Type u₄} [Category.{v₄} J]

/-- Colimit preservation descends along a colimit-preserving functor with a
right inverse up to natural isomorphism. In particular this applies to a reflector. -/
theorem preservesColimitsOfShape_of_reflector (L : D ⥤ C) (R : C ⥤ D)
    (U : C ⥤ E) (e : R ⋙ L ≅ 𝟭 C) [HasColimitsOfShape J D]
    [PreservesColimitsOfShape J L] [PreservesColimitsOfShape J (L ⋙ U)] :
    PreservesColimitsOfShape J U where
  preservesColimit {K} := by
    have : PreservesColimit ((K ⋙ R) ⋙ L) U :=
      preservesColimit_of_preserves_colimit_cocone
        (isColimitOfPreserves L (colimit.isColimit (K ⋙ R)))
        (isColimitOfPreserves (L ⋙ U) (colimit.isColimit (K ⋙ R)))
    exact preservesColimit_of_iso_diagram U
      (Functor.associator K R L ≪≫ Functor.isoWhiskerLeft K e ≪≫ K.rightUnitor)

end CategoryTheory.Limits
