/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.DerivedCategory.ExtRightDerivedNaturality

/-! # The explicit map underlying the Ext and resolution comparison -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] CategoryTheory.enoughInjectives_of_hasInjectiveResolutions
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open HomologicalComplex
universe w v u
namespace CategoryTheory.InjectiveResolution
variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
  [HasExt.{w} C] {Y : C} (I : InjectiveResolution Y) (X : C) (n : ℕ)

attribute [local instance] HasDerivedCategory.standard

/-- The inverse comparison is the actual localized cocycle map, followed by the inverse
of the shifted injective-resolution augmentation. -/
theorem extRightDerivedAddEquiv_symm_hom
    (y : ((preadditiveCoyoneda.obj (Opposite.op X)).rightDerived n).obj Y) :
    ((I.extRightDerivedAddEquiv X n).symm y).hom =
      CochainComplex.HomComplex.CohomologyClass.derivedHomAddEquiv _ _ (n : ℤ)
        (CochainComplex.HomComplex.homologyAddEquiv _ _ (n : ℤ)
          ((I.homComplexHomologyRightDerivedIso X n).inv y)) ≫
        (shiftFunctor _ (n : ℤ)).map (inv (DerivedCategory.Q.map I.extendedι)) := by
  change (I.extEquivCohomologyClass.symm
    (CochainComplex.HomComplex.homologyAddEquiv _ _ (n : ℤ)
      ((I.homComplexHomologyRightDerivedIso X n).inv y))).hom = _
  obtain ⟨z, hz⟩ := CochainComplex.HomComplex.CohomologyClass.mk_surjective
    (CochainComplex.HomComplex.homologyAddEquiv _ _ (n : ℤ)
      ((I.homComplexHomologyRightDerivedIso X n).inv y))
  rw [← hz, I.extEquivCohomologyClass_symm_mk_hom,
    CochainComplex.HomComplex.CohomologyClass.derivedHomAddEquiv_mk]
  simp only [DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, NatTrans.id_app,
    Iso.refl_inv, ShiftedHom.mk₀_id_comp, ShiftedHom.comp_mk₀, ShiftedHom.map,
    Category.assoc]
  erw [Category.comp_id]
  rfl

end CategoryTheory.InjectiveResolution
