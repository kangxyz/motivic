/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.DerivedCategory.ExtRightDerivedNaturality
public import Motivic.Aglib.Algebra.Homology.DerivedCategory.ExtRightDerivedMap

/-! # Original Ext functoriality of the resolution comparison -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open HomologicalComplex CochainComplex.HomComplex
universe w v u
namespace CategoryTheory.InjectiveResolution
variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
  [HasExt.{w} C] {Y : C} (I : InjectiveResolution Y) {X X' : C} (f : X' ⟶ X) (n : ℕ)
attribute [local instance] HasDerivedCategory.standard

/-- Actual precomposition on original Ext agrees with the genuine right-derived source map. -/
theorem extRightDerivedAddEquiv_symm_naturality_left
    (y : ((preadditiveCoyoneda.obj (Opposite.op X)).rightDerived n).obj Y) :
    (Abelian.Ext.mk₀ f).comp ((I.extRightDerivedAddEquiv X n).symm y) (zero_add n) =
      (I.extRightDerivedAddEquiv X' n).symm
        ((NatTrans.rightDerived (preadditiveCoyoneda.map f.op) n).app Y y) := by
  have hi : (NatTrans.rightDerived (preadditiveCoyoneda.map f.op) n).app Y ≫
        (I.homComplexHomologyRightDerivedIso X' n).inv =
      (I.homComplexHomologyRightDerivedIso X n).inv ≫
        homologyMap (CochainComplex.HomComplex.map
          ((CochainComplex.singleFunctor C 0).map f) (𝟙 _)) (n : ℤ) := by
    apply (cancel_epi (I.homComplexHomologyRightDerivedIso X n).hom).1
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [← I.homComplexHomologyRightDerivedIso_naturality_left f n,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hy := ConcreteCategory.congr_hom hi y
  change (I.homComplexHomologyRightDerivedIso X' n).inv
      ((NatTrans.rightDerived (preadditiveCoyoneda.map f.op) n).app Y y) =
    homologyMap (CochainComplex.HomComplex.map
      ((CochainComplex.singleFunctor C 0).map f) (𝟙 _)) (n : ℤ)
      ((I.homComplexHomologyRightDerivedIso X n).inv y) at hy
  apply Abelian.Ext.ext
  rw [Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom, ShiftedHom.mk₀_comp,
    I.extRightDerivedAddEquiv_symm_hom, I.extRightDerivedAddEquiv_symm_hom]
  change (DerivedCategory.singleFunctor C 0).map f ≫ _ =
    CohomologyClass.derivedHomAddEquiv _ _ (n : ℤ)
      (homologyAddEquiv _ _ (n : ℤ) ((I.homComplexHomologyRightDerivedIso X' n).inv
        ((NatTrans.rightDerived (preadditiveCoyoneda.map f.op) n).app Y y))) ≫ _
  rw [hy, homologyAddEquiv_naturality, CohomologyClass.derivedHomAddEquiv_naturality]
  change DerivedCategory.Q.map ((CochainComplex.singleFunctor C 0).map f) ≫ _ = _
  simp [Category.assoc]

/-- Forward form of source naturality for the original Ext comparison. -/
theorem extRightDerivedAddEquiv_naturality_left (x : Abelian.Ext.{w} X Y n) :
    I.extRightDerivedAddEquiv X' n ((Abelian.Ext.mk₀ f).comp x (zero_add n)) =
      (NatTrans.rightDerived (preadditiveCoyoneda.map f.op) n).app Y
        (I.extRightDerivedAddEquiv X n x) := by
  obtain ⟨y, rfl⟩ := (I.extRightDerivedAddEquiv X n).symm.surjective x
  rw [I.extRightDerivedAddEquiv_symm_naturality_left f n]
  rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

end CategoryTheory.InjectiveResolution
