/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.HomotopyCategory.HomComplexSingleIso
public import Aglib.Algebra.Homology.Embedding.MapExtend.Naturality
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

namespace CategoryTheory

/-- Existing injective resolutions already supply injective presentations.
Use this locally when calling the canonical enough-injectives comparisons. -/
theorem enoughInjectives_of_hasInjectiveResolutions
    {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C] :
    EnoughInjectives C where
  presentation X :=
    let I := injectiveResolution X
    ⟨{ J := I.cocomplex.X 0, f := I.ι.f 0 }⟩

end CategoryTheory
