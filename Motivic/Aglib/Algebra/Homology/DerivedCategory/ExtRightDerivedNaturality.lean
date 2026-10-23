/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.DerivedCategory.ExtRightDerived
public import Motivic.Aglib.Algebra.Homology.HomotopyCategory.HomComplexNaturality

/-! # Naturality of the actual Ext and injective-resolution comparison -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] CategoryTheory.enoughInjectives_of_hasInjectiveResolutions
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open HomologicalComplex
universe w v u
namespace CochainComplex.HomComplex.CohomologyClass
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {K K' L L' : CochainComplex C ℤ} [L.IsKInjective] [L'.IsKInjective] (n : ℤ)

/-- On an actual cocycle the comparison is localization of its chain map. -/
theorem derivedHomAddEquiv_mk (z : Cocycle K L n) :
    derivedHomAddEquiv K L n (mk z) =
      DerivedCategory.Q.map (Cocycle.equivHomShift.symm z) ≫
        (DerivedCategory.Q.commShiftIso n).hom.app L := by
  change (DerivedCategory.quotientCompQhIso C).inv.app K ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient C _).map
      (Cocycle.equivHomShift.symm z)) ≫
    (DerivedCategory.quotientCompQhIso C).hom.app (L⟦n⟧) ≫
    (DerivedCategory.Q.commShiftIso n).hom.app L = _
  rw [← Functor.comp_map, (DerivedCategory.quotientCompQhIso C).hom.naturality_assoc]
  simp

/-- Both arguments retain the original chain maps after localization. -/
theorem derivedHomAddEquiv_naturality (f : K' ⟶ K) (g : L ⟶ L')
    (x : CohomologyClass K L n) :
    derivedHomAddEquiv K' L' n (classMap f g n x) =
      DerivedCategory.Q.map f ≫ derivedHomAddEquiv K L n x ≫
        (DerivedCategory.Q.map g)⟦n⟧' := by
  obtain ⟨z, rfl⟩ := mk_surjective x
  rw [classMap_mk, derivedHomAddEquiv_mk, derivedHomAddEquiv_mk,
    Cocycle.equivHomShift_symm_postcomp, Cocycle.equivHomShift_symm_precomp]
  simp only [Functor.map_comp, Category.assoc]
  exact congrArg (fun a => DerivedCategory.Q.map f ≫
    DerivedCategory.Q.map (Cocycle.equivHomShift.symm z) ≫ a)
      ((DerivedCategory.Q.commShiftIso n).hom.naturality g)

end CochainComplex.HomComplex.CohomologyClass

namespace CategoryTheory.InjectiveResolution
variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
  {Y : C} (I : InjectiveResolution Y) {X X' : C} (f : X' ⟶ X) (n : ℕ)

/-- Source functoriality of the original Nat-index resolution comparison. -/
@[reassoc]
theorem homComplexHomologyRightDerivedIso_naturality_left :
    homologyMap (CochainComplex.HomComplex.map
      ((CochainComplex.singleFunctor C 0).map f) (𝟙 _)) (n : ℤ) ≫
        (I.homComplexHomologyRightDerivedIso X' n).hom =
      (I.homComplexHomologyRightDerivedIso X n).hom ≫
        (NatTrans.rightDerived (preadditiveCoyoneda.map f.op) n).app Y := by
  change (homologyFunctor AddCommGrpCat (ComplexShape.up ℤ) (n : ℤ)).map
    (CochainComplex.HomComplex.map ((CochainComplex.singleFunctor C 0).map f) (𝟙 _)) ≫ _ = _
  rw [I.rightDerived_app_eq]
  dsimp only [homComplexHomologyRightDerivedIso, isoRightDerivedObjCochain,
    cochainComplex, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_hom, Functor.mapIso_inv]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Functor.map_comp_assoc, CochainComplex.homComplexSingleIso_naturality]
  simp only [Functor.map_comp, Functor.map_id, Category.comp_id, Category.assoc]
  rw [cancel_epi]
  rw [← Functor.map_comp_assoc, mapExtendIso_hom_natTrans]
  simp only [Functor.map_comp, Category.assoc]
  rw [cancel_epi, ← Category.assoc, ← Category.assoc, cancel_mono]
  exact extendHomologyIso_hom_naturality
    ((NatTrans.mapHomologicalComplex (preadditiveCoyoneda.map f.op) _).app I.cocomplex)
    ComplexShape.embeddingUpNat (j := n) rfl

/-- Coefficient naturality uses a genuine lift between the chosen injective resolutions. -/
@[reassoc]
theorem homComplexHomologyRightDerivedIso_naturality_right
    {Z : C} (g : Y ⟶ Z) (J : InjectiveResolution Z)
    (φ : I.cocomplex ⟶ J.cocomplex) (hφ : I.ι.f 0 ≫ φ.f 0 = g ≫ J.ι.f 0) (P : C) :
    homologyMap (CochainComplex.HomComplex.map (𝟙 _)
      (extendMap φ ComplexShape.embeddingUpNat)) (n : ℤ) ≫
        (J.homComplexHomologyRightDerivedIso P n).hom =
      (I.homComplexHomologyRightDerivedIso P n).hom ≫
        ((preadditiveCoyoneda.obj (Opposite.op P)).rightDerived n).map g := by
  change (homologyFunctor AddCommGrpCat (ComplexShape.up ℤ) (n : ℤ)).map
    (CochainComplex.HomComplex.map (𝟙 _) (extendMap φ ComplexShape.embeddingUpNat)) ≫ _ = _
  dsimp only [homComplexHomologyRightDerivedIso, isoRightDerivedObjCochain,
    cochainComplex, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_hom, Functor.mapIso_inv]
  simp only [Category.assoc]
  rw [I.isoRightDerivedObj_inv_naturality g J φ hφ]
  rw [← Functor.map_comp_assoc]
  have hs := CochainComplex.homComplexSingleIso_naturality (𝟙 P)
    (extendMap φ ComplexShape.embeddingUpNat)
  simp only [op_id, Functor.map_id, NatTrans.mapHomologicalComplex_id,
    NatTrans.id_app, Category.id_comp] at hs
  rw [hs]
  simp only [Functor.map_comp, Category.assoc]
  rw [cancel_epi]
  rw [← Functor.map_comp_assoc, mapExtendIso_hom_naturality]
  simp only [Functor.map_comp, Category.assoc]
  rw [cancel_epi, ← Category.assoc, ← Category.assoc, cancel_mono]
  exact extendHomologyIso_hom_naturality
    (((preadditiveCoyoneda.obj (Opposite.op P)).mapHomologicalComplex _).map φ)
    ComplexShape.embeddingUpNat (j := n) rfl

end CategoryTheory.InjectiveResolution
