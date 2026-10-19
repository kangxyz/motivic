/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.CategoryTheory.Sites.SheafProducts.ObjectwiseExact
public import Mathlib.CategoryTheory.Limits.Types.Products

/-! # Sections of the actual categorical sheaf product -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
universe u
namespace CategoryTheory.Sheaf.Products
variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
  {I : Type u} (A : I → Sheaf J AddCommGrpCat.{u + 1}) (U : C)

/-- Actual product projections identify sections bijectively with the coordinate sections. -/
theorem sections_bijective : Function.Bijective
    (fun s : (∏ᶜ A).obj.obj (op U) ↦ fun i ↦ (Limits.Pi.π A i).hom.app (op U) s) := by
  let E : Sheaf J AddCommGrpCat.{u + 1} ⥤ Type (u + 1) :=
    sheafToPresheaf J AddCommGrpCat ⋙ (evaluation Cᵒᵖ AddCommGrpCat).obj (op U) ⋙
      forget AddCommGrpCat
  let e := asIso (piComparison E A) ≪≫ Types.productIso.{u, u + 1} (fun i ↦ E.obj (A i))
  have he : Function.Bijective e.hom := ConcreteCategory.bijective_of_isIso e.hom
  have hcoord (s) (i) : e.hom s i = (Limits.Pi.π A i).hom.app (op U) s := by
    have h : e.hom ≫ (↾fun f => f i) = E.map (Limits.Pi.π A i) := by
      dsimp only [e, Iso.trans_hom, asIso_hom]
      rw [Category.assoc, Types.productIso_hom_comp_eval, piComparison_comp_π]
    exact ConcreteCategory.congr_hom h s
  have hfun : (fun s : (∏ᶜ A).obj.obj (op U) ↦
      fun i ↦ (Limits.Pi.π A i).hom.app (op U) s) = e.hom := by
    funext s i
    exact (hcoord s i).symm
  rw [hfun]
  exact he

/-- This is the additive equivalence defined by the original categorical projections. -/
def sectionsEquiv : (∏ᶜ A).obj.obj (op U) ≃+ ∀ i, (A i).obj.obj (op U) :=
  AddEquiv.ofBijective
    (show (∏ᶜ A).obj.obj (op U) →+ ∀ i, (A i).obj.obj (op U) from
    { toFun := fun s i ↦ (Limits.Pi.π A i).hom.app (op U) s
      map_zero' := funext fun _ ↦ map_zero _
      map_add' s t := funext fun _ ↦ map_add _ s t })
    (sections_bijective J A U)

end CategoryTheory.Sheaf.Products
