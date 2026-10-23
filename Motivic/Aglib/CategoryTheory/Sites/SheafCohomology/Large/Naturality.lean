/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Large.Basic

/-!
# Actual maps in the ordinary-cohomology and hypercohomology comparison

The comparison uses the Ext/derived-Hom equivalence. These equations verify
actual restriction and coefficient maps, including the affine-line projection
when this general construction is specialized to the smooth Nisnevich site.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Abelian Opposite

universe w w' t v u

namespace CategoryTheory.Sheaf.LargeCohomology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v t}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{max v t})]
  [HasDerivedCategory.{w'} (Sheaf J AddCommGrpCat.{max v t})]

/-- The derived morphism of the compared Ext class is the original morphism. -/
@[simp] theorem singleComparison_hom (F : Sheaf J AddCommGrpCat.{max v t})
    (n : ℕ) (X : C)
    (x : Hypercohomology.H J ((CochainComplex.singleFunctor _ 0).obj F) (n : ℤ) X) :
    (dsimp% only [Functor.op_obj] (singleComparison J F n X x).hom) = x :=
  Ext.homAddEquiv.apply_symm_apply x

/-- The single-complex comparison commutes with actual restrictions on the site. -/
theorem singleComparison_restriction (F : Sheaf J AddCommGrpCat.{max v t})
    (n : ℕ) {X Y : C} (f : X ⟶ Y)
    (x : Hypercohomology.H J ((CochainComplex.singleFunctor _ 0).obj F) (n : ℤ) Y) :
    singleComparison J F n X
        (Hypercohomology.restriction J ((CochainComplex.singleFunctor _ 0).obj F)
          (n : ℤ) f x) =
      (presheaf J F n).map f.op (singleComparison J F n Y x) := by
  apply Ext.ext
  rw [singleComparison_hom, restriction_apply, Ext.comp_hom, Ext.mk₀_hom,
    ShiftedHom.mk₀_comp, singleComparison_hom]
  rfl

/-- The single-complex comparison commutes with the actual map of coefficient sheaves. -/
theorem singleComparison_coefficient {F G : Sheaf J AddCommGrpCat.{max v t}}
    (η : F ⟶ G) (n : ℕ) (X : C)
    (x : Hypercohomology.H J ((CochainComplex.singleFunctor _ 0).obj F) (n : ℤ) X) :
    singleComparison J G n X
        (Hypercohomology.map J ((CochainComplex.singleFunctor _ 0).map η) (n : ℤ) X x) =
      ((presheafFunctor J n).map η).app (op X) (singleComparison J F n X x) := by
  apply Ext.ext
  change (singleComparison J G n X _).hom =
    ((singleComparison J F n X x).comp (Ext.mk₀ η) (add_zero n)).hom
  rw [singleComparison_hom, Ext.comp_hom, Ext.mk₀_hom,
    ShiftedHom.comp_mk₀, singleComparison_hom]
  rfl

end CategoryTheory.Sheaf.LargeCohomology
