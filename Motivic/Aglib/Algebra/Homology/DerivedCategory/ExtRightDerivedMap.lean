/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.DerivedCategory.ExtRightDerived

/-! # The explicit map underlying the Ext and resolution comparison -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
  change _ = CochainComplex.HomComplex.CohomologyClass.derivedHomAddEquiv _ _ (n : ℤ)
    (CochainComplex.HomComplex.homologyAddEquiv _ _ (n : ℤ)
      ((I.homComplexHomologyRightDerivedIso X n).inv.hom y)) ≫ _
  simp [extRightDerivedAddEquiv, Iso.homCongrAddEquiv, Iso.homCongr,
    ← Abelian.Ext.homAddEquiv_apply]; rfl

end CategoryTheory.InjectiveResolution
