/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.HomotopyCategory.HomComplexSingleIso
public import Motivic.Aglib.Algebra.Homology.Embedding.MapExtend
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.Abelian.RightDerived

/-! # Computing derived-category Ext using an actual injective resolution -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open HomologicalComplex
universe w v u
namespace CategoryTheory
variable {C : Type u} [Category.{v} C]

/-- The additive version of conjugation by actual isomorphisms. -/
def Iso.homCongrAddEquiv [Preadditive C] {X Y X' Y' : C} (e : X ≅ X') (f : Y ≅ Y') :
    (X ⟶ Y) ≃+ (X' ⟶ Y') where
  toEquiv := Iso.homCongr e f
  map_add' a b := by simp [Iso.homCongr]

namespace InjectiveResolution
variable [Abelian C] {Y : C} (I : InjectiveResolution Y)

/-- The actual augmentation of the resolution extended by zero to integer degrees. -/
def extendedι : (CochainComplex.singleFunctor C 0).obj Y ⟶
    I.cocomplex.extend ComplexShape.embeddingUpNat :=
  (extendSingleIso ComplexShape.embeddingUpNat Y 0 0 rfl).inv ≫
    extendMap I.ι ComplexShape.embeddingUpNat

instance extendedι_quasiIso : QuasiIso I.extendedι := by
  dsimp only [extendedι]
  infer_instance

end InjectiveResolution

end CategoryTheory

namespace CochainComplex.HomComplex.CohomologyClass
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  (K L : CochainComplex C ℤ) [L.IsKInjective] (n : ℤ)

/-- Cohomology of the Hom complex maps to the derived category by the actual localization. -/
def derivedHomAddEquiv : CohomologyClass K L n ≃+
    (DerivedCategory.Q.obj K ⟶ (DerivedCategory.Q.obj L)⟦n⟧) :=
  (homAddEquiv (K := K) (L := L) (n := n)).trans
    ((AddEquiv.ofBijective DerivedCategory.Qh.mapAddHom
      (CochainComplex.IsKInjective.Qh_map_bijective _ _)).trans
      (Iso.homCongrAddEquiv ((DerivedCategory.quotientCompQhIso C).app K)
        (((DerivedCategory.quotientCompQhIso C).app (L⟦n⟧)) ≪≫
          (DerivedCategory.Q.commShiftIso n).app L)))

end CochainComplex.HomComplex.CohomologyClass

namespace CategoryTheory.InjectiveResolution
variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
  [HasExt.{w} C] {Y : C} (I : InjectiveResolution Y) (X : C) (n : ℕ)

/-- Integer Hom-complex homology computes the original Nat-index derived Hom functor. -/
def homComplexHomologyRightDerivedIso :
    (CochainComplex.HomComplex ((CochainComplex.singleFunctor C 0).obj X)
      (I.cocomplex.extend ComplexShape.embeddingUpNat)).homology (n : ℤ) ≅
      ((preadditiveCoyoneda.obj (Opposite.op X)).rightDerived n).obj Y :=
  (HomologicalComplex.homologyFunctor _ _ (n : ℤ)).mapIso
      (CochainComplex.homComplexSingleIso X _) ≪≫
    (HomologicalComplex.homologyFunctor _ _ (n : ℤ)).mapIso
      (I.cocomplex.mapExtendIso (preadditiveCoyoneda.obj (Opposite.op X))
        ComplexShape.embeddingUpNat) ≪≫
    (((preadditiveCoyoneda.obj (Opposite.op X)).mapHomologicalComplex _).obj
      I.cocomplex).extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl ≪≫
    (I.isoRightDerivedObj (preadditiveCoyoneda.obj (Opposite.op X)) n).symm

/-- Derived-category Ext is computed by the actual Nat-index injective resolution. -/
def extRightDerivedAddEquiv : Abelian.Ext.{w} X Y n ≃+
    ((preadditiveCoyoneda.obj (Opposite.op X)).rightDerived n).obj Y := by
  let := HasDerivedCategory.standard C
  exact Abelian.Ext.homAddEquiv.trans
    ((Iso.homCongrAddEquiv (Iso.refl _)
      ((shiftFunctor _ (n : ℤ)).mapIso (asIso (DerivedCategory.Q.map I.extendedι)))).trans
      ((CochainComplex.HomComplex.CohomologyClass.derivedHomAddEquiv _ _ (n : ℤ)).symm.trans
        ((CochainComplex.HomComplex.homologyAddEquiv _ _ (n : ℤ)).symm.trans
          (I.homComplexHomologyRightDerivedIso X n).addCommGroupIsoToAddEquiv)))

end CategoryTheory.InjectiveResolution
