/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Products of sectionwise-surjective ordinary sheaf morphisms

This does not assert that arbitrary products of sheaf epimorphisms are epimorphisms.
The stronger epimorphism hypothesis is on the underlying presheaf morphisms.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
namespace CategoryTheory.Sheaf.Products
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {I : Type v} (A B : I → Sheaf J AddCommGrpCat.{max u v}) (a : ∀ i, A i ⟶ B i)

/-- The original sheaf product map is epimorphic when every factor is already
surjective as a presheaf map. -/
theorem presheaf_epi_piMap_of_presheaf_epi [∀ i, Epi (a i).hom] :
    Epi (Limits.Pi.map a).hom := by
  let E := sheafToPresheaf J AddCommGrpCat.{max u v}
  let : AB4StarOfSize.{v} AddCommGrpCat.{max u v} := AB4StarOfSize_shrink _
  have (i : I) : Epi (E.map (a i)) := inferInstanceAs (Epi (a i).hom)
  have hnat : Epi (Discrete.natTrans
      (F := Discrete.functor (fun i => E.obj (A i)))
      (G := Discrete.functor (fun i => E.obj (B i)))
      (fun i => E.map (a i.as))) := by
    let (i : Discrete I) : Epi ((Discrete.natTrans
        (F := Discrete.functor (fun i => E.obj (A i)))
        (G := Discrete.functor (fun i => E.obj (B i)))
        (fun i => E.map (a i.as))).app i) := inferInstanceAs (Epi (a i.as).hom)
    exact NatTrans.epi_of_epi_app _
  have hepi : Epi (Limits.Pi.map (fun i => E.map (a i))) := by
    change Epi ((lim : (Discrete I ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ _).map
      (Discrete.natTrans
        (F := Discrete.functor (fun i => E.obj (A i)))
        (G := Discrete.functor (fun i => E.obj (B i)))
        (fun i => E.map (a i.as))))
    infer_instance
  have h : E.map (Limits.Pi.map a) ≫ piComparison E B =
      piComparison E A ≫ Limits.Pi.map (fun i => E.map (a i)) := by
    apply Limits.Pi.hom_ext
    intro i
    simp only [Category.assoc, piComparison_comp_π, Limits.Pi.map_π,
      ← E.map_comp, piComparison_comp_π_assoc]
  have : Epi (E.map (Limits.Pi.map a) ≫ piComparison E B) := by
    rw [h]
    infer_instance
  have : Epi (E.map (Limits.Pi.map a)) :=
    (epi_comp_iff_of_isIso _ (piComparison E B)).mp inferInstance
  exact this

/-- In particular, the product is an epimorphism in the original sheaf category. -/
theorem epi_piMap_of_presheaf_epi [∀ i, Epi (a i).hom] : Epi (Limits.Pi.map a) := by
  have := presheaf_epi_piMap_of_presheaf_epi J A B a
  exact (sheafToPresheaf J AddCommGrpCat.{max u v}).epi_of_epi_map
    (presheaf_epi_piMap_of_presheaf_epi J A B a)

end CategoryTheory.Sheaf.Products
