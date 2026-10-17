/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.HomotopyCategory.HomComplexNaturality
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-! # The hom complex from a single object is the ordinary Hom-valued complex -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
universe v u
namespace CochainComplex
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

/-- This isomorphism evaluates a cochain at the original object in degree zero. -/
def homComplexSingleIso (X : C) (K : CochainComplex C ℤ) :
    HomComplex ((singleFunctor C 0).obj X) K ≅
      ((preadditiveCoyoneda.obj (Opposite.op X)).mapHomologicalComplex _).obj K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (HomComplex.Cochain.fromSingleEquiv (X := X) (K := K)
      (show (0 : ℤ) + n = n by simp)).toAddCommGrpIso)
    (by
      intro i j hij
      ext α
      obtain ⟨f, rfl⟩ := HomComplex.Cochain.fromSingleMk_surjective α i (by simp)
      symm
      simpa using congrArg
        (HomComplex.Cochain.fromSingleEquiv (X := X) (K := K)
          (show (0 : ℤ) + j = j by simp))
        (HomComplex.Cochain.δ_fromSingleMk f (show (0 : ℤ) + i = i by simp) j j (by simp)))

/-- Evaluation at the original object respects actual source and coefficient maps. -/
@[reassoc]
theorem homComplexSingleIso_naturality {X X' : C} (f : X' ⟶ X)
    {K L : CochainComplex C ℤ} (g : K ⟶ L) :
    HomComplex.map ((singleFunctor C 0).map f) g ≫ (homComplexSingleIso X' L).hom =
      (homComplexSingleIso X K).hom ≫
        (NatTrans.mapHomologicalComplex (preadditiveCoyoneda.map f.op) _).app K ≫
        ((preadditiveCoyoneda.obj (Opposite.op X')).mapHomologicalComplex _).map g := by
  ext n α
  obtain ⟨h, rfl⟩ := HomComplex.Cochain.fromSingleMk_surjective α n (by simp)
  change HomComplex.Cochain.fromSingleEquiv (show (0 : ℤ) + n = n by simp)
      (((HomComplex.Cochain.ofHom ((singleFunctor C 0).map f)).comp
        (HomComplex.Cochain.fromSingleMk h (show (0 : ℤ) + n = n by simp)) (zero_add n)).comp
        (HomComplex.Cochain.ofHom g) (add_zero n)) = _
  rw [← HomComplex.Cochain.fromSingleMk_precomp, ← HomComplex.Cochain.fromSingleMk_postcomp]
  simp only [homComplexSingleIso, HomComplex.Cochain.fromSingleEquiv_fromSingleMk]
  simp only [Category.assoc, HomComplex_X, preadditiveCoyoneda_obj,
    Functor.mapHomologicalComplex_obj_X, Functor.comp_obj, ModuleCat.forget₂_obj,
    preadditiveCoyonedaObj_obj_carrier, HomologicalComplex.comp_f,
    HomologicalComplex.Hom.isoOfComponents_hom_f, AddEquiv.toAddCommGrpIso_hom,
    AddEquiv.toAddMonoidHom_eq_coe, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplex_map_f, Functor.comp_map, preadditiveCoyonedaObj_map,
    ModuleCat.forget₂_map, ConcreteCategory.hom_ofHom, AddCommGrpCat.hom_comp,
    AddMonoidHom.coe_comp, AddMonoidHom.coe_coe, LinearMap.coe_mk, AddHom.coe_mk,
    Function.comp_apply, HomComplex.Cochain.fromSingleEquiv_fromSingleMk]
  change f ≫ h ≫ g.f n = (f ≫ h) ≫ g.f n
  exact (Category.assoc _ _ _).symm

end CochainComplex
