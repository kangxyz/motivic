/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Large.Basic


/-!
# Degree-zero ordinary cohomology and sections

The actual Ext-based degree-zero cohomology agrees naturally with sections.
The section equivalence retains restriction along every site morphism and
naturality in the coefficient sheaf. Transfer actions are supplied by host
consumers; they are not constructed in this general cohomology leaf.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian Opposite

universe w t v u

namespace CategoryTheory.Sheaf.Hypercohomology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v t}]

set_option backward.isDefEq.respectTransparency false in
/-- The section-representing equivalence respects every actual site morphism. -/
theorem sectionsAddEquiv_naturality_left {X Y : C} (f : X ⟶ Y)
    (F : Sheaf J AddCommGrpCat.{max v t}) (h : freeAbelianSheaf J Y ⟶ F) :
    sectionsAddEquiv J X F ((freeAbelianSheafFunctor J).map f ≫ h) =
      F.obj.map f.op (sectionsAddEquiv J Y F h) := by
  change uliftYonedaEquiv.{t}
      (((AddCommGrpCat.adj.{max v t}.whiskerRight Cᵒᵖ).homEquiv _ F.obj)
        (((sheafificationAdjunction J AddCommGrpCat.{max v t}).homEquiv _ F)
          ((freeAbelianSheafFunctor J).map f ≫ h))) = _
  dsimp only [freeAbelianSheafFunctor, Functor.comp_map]
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left]
  exact (uliftYonedaEquiv_naturality _ f.op).symm

end CategoryTheory.Sheaf.Hypercohomology

namespace CategoryTheory.Sheaf.LargeCohomology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v t}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{max v t})]

/-- Actual Ext-based degree-zero ordinary cohomology is the section group. -/
def zeroSections (F : Sheaf J AddCommGrpCat.{max v t}) (X : C) :
    H J F 0 X ≃+ F.obj.obj (op X) :=
  Ext.addEquiv₀.trans (Hypercohomology.sectionsAddEquiv J X F)

/-- The comparison respects restrictions along every actual site morphism. -/
theorem zeroSections_restriction (F : Sheaf J AddCommGrpCat.{max v t})
    {X Y : C} (f : X ⟶ Y) (x : H J F 0 Y) :
    zeroSections J F X ((presheaf J F 0).map f.op x) =
      F.obj.map f.op (zeroSections J F Y x) := by
  obtain ⟨h, rfl⟩ := Ext.addEquiv₀.symm.surjective x
  change Hypercohomology.sectionsAddEquiv J X F
      (Ext.addEquiv₀ ((Ext.mk₀ ((Hypercohomology.freeAbelianSheafFunctor J).map f)).comp
        (Ext.mk₀ h) (zero_add 0))) =
      F.obj.map f.op (Hypercohomology.sectionsAddEquiv J Y F (Ext.addEquiv₀ (Ext.mk₀ h)))
  rw [Ext.mk₀_comp_mk₀]
  change Hypercohomology.sectionsAddEquiv J X F
      (Ext.addEquiv₀ (Ext.addEquiv₀.symm _)) =
    F.obj.map f.op (Hypercohomology.sectionsAddEquiv J Y F
      (Ext.addEquiv₀ (Ext.addEquiv₀.symm h)))
  simp only [AddEquiv.apply_symm_apply]
  exact Hypercohomology.sectionsAddEquiv_naturality_left J f F h

/-- The comparison also respects actual coefficient sheaf morphisms. -/
theorem zeroSections_naturality {F G : Sheaf J AddCommGrpCat.{max v t}}
    (η : F ⟶ G) (X : C) (x : H J F 0 X) :
    zeroSections J G X (((presheafFunctor J 0).map η).app (op X) x) =
      η.hom.app (op X) (zeroSections J F X x) := by
  obtain ⟨h, rfl⟩ := Ext.addEquiv₀.symm.surjective x
  change Hypercohomology.sectionsAddEquiv J X G
      (Ext.addEquiv₀ ((Ext.mk₀ h).comp (Ext.mk₀ η) (add_zero 0))) =
    η.hom.app (op X) (Hypercohomology.sectionsAddEquiv J X F (Ext.addEquiv₀ (Ext.mk₀ h)))
  rw [Ext.mk₀_comp_mk₀]
  change Hypercohomology.sectionsAddEquiv J X G
      (Ext.addEquiv₀ (Ext.addEquiv₀.symm _)) =
    η.hom.app (op X) (Hypercohomology.sectionsAddEquiv J X F
      (Ext.addEquiv₀ (Ext.addEquiv₀.symm h)))
  simp only [AddEquiv.apply_symm_apply]
  exact Hypercohomology.sectionsEquiv_naturality J X h η

end CategoryTheory.Sheaf.LargeCohomology
