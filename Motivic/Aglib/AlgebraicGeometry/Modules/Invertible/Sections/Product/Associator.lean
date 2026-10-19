/-
Copyright (c) 2026 Motivic Cohomology contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Sections.Product.Ideals
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorFunctorAssociator

/-! # Products retain the canonical line-bundle associator -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite
  SheafOfModulesOfCommRing
open Scheme.Modules Scheme.Modules.Invertible
open scoped TensorProduct
universe u
namespace AlgebraicGeometry.Scheme.Modules.Hom

private theorem map_unit_apply (X : Scheme.{u})
    {P Q : PresheafOfModulesOfCommRing.{u} X.sheaf.obj} (f : P ⟶ Q)
    (U : X.Opens) (x : P.obj (op U)) :
    ((associatedSheaf X.sheaf).map f).val.app (op U)
        (((associatedSheafUnit X.sheaf).app P).app (op U) x) =
      ((associatedSheafUnit X.sheaf).app Q).app (op U) (f.app (op U) x) := by
  exact (congrArg (fun q => q.app (op U) x)
    ((associatedSheafUnit X.sheaf).naturality f)).symm

set_option maxHeartbeats 800000 in
-- Comparing the three nested sheafification units requires extra definitional reduction.
theorem product_comparison {X : Scheme.{u}} (L M N : X.Modules)
    (a : L ⟶ SheafOfModules.unit X.ringCatSheaf)
    (b : M ⟶ SheafOfModules.unit X.ringCatSheaf)
    (c : N ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (lineTensorRightUnitComparison X L M).app N ≫ productSection (productSection a b) c =
      (lineTensorPresheafAssociator X L M).hom.app N ≫
        (lineTensorLeftUnitComparison X L M).app N ≫ productSection a (productSection b c) := by
  apply (PresheafOfModules.sheafificationAdjunction
    (R := X.ringCatSheaf) (𝟙 _)).homEquiv _ _ |>.injective
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro lm n
  induction lm using TensorProduct.inductionOn with
  | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
  | tmul l m =>
    let A := (SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj L
    let B := (SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj M
    let C := (SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj N
    let η := associatedSheafUnit X.sheaf
    change (productSection (productSection a b) c).app U.unop
      (((associatedSheaf X.sheaf).map (η.app (A ⊗ B) ⊗ₘ 𝟙 C)).val.app U
        ((η.app ((A ⊗ B) ⊗ C)).app U ((l ⊗ₜ[X.sheaf.obj.obj U] m) ⊗ₜ[X.sheaf.obj.obj U] n))) =
      (productSection a (productSection b c)).app U.unop
      (((associatedSheaf X.sheaf).map (𝟙 A ⊗ₘ η.app (B ⊗ C))).val.app U
        (((associatedSheaf X.sheaf).map (α_ A B C).hom).val.app U
          ((η.app ((A ⊗ B) ⊗ C)).app U ((l ⊗ₜ[X.sheaf.obj.obj U] m) ⊗ₜ[X.sheaf.obj.obj U] n))))
    erw [map_unit_apply X (η.app (A ⊗ B) ⊗ₘ 𝟙 C) U.unop
      ((l ⊗ₜ[X.sheaf.obj.obj U] m) ⊗ₜ[X.sheaf.obj.obj U] n)]
    erw [map_unit_apply X (α_ A B C).hom U.unop
      ((l ⊗ₜ[X.sheaf.obj.obj U] m) ⊗ₜ[X.sheaf.obj.obj U] n)]
    erw [map_unit_apply X (𝟙 A ⊗ₘ η.app (B ⊗ C)) U.unop]
    change (productSection (productSection a b) c).app U.unop
      (moduleTensorSection X _ _ U.unop (moduleTensorSection X L M U.unop l m) n) =
      (productSection a (productSection b c)).app U.unop
      (moduleTensorSection X _ _ U.unop l (moduleTensorSection X M N U.unop m n))
    simp only [productSection_tensor, mul_assoc]

/-- The literal three-factor product is compatible with the native left-to-right associator. -/
theorem productSection_associator {X : Scheme.{u}} (L M N : LineBundle X)
    (a : L.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    (b : M.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    (c : N.val ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (tensorLineBundleAssociator X L M N).hom ≫ productSection a (productSection b c) =
      productSection (productSection a b) c := by
  let P := PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) L.val.val M.val.val
  let f := PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf)
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P)
    (𝟙 N.val.val)
  let e := sheafificationMapIsoOfLocallyBijective X f
    (tensorUnitWhiskerRight_locallyBijective X L.val M.val N.val L.property M.property)
  apply (cancel_epi e.hom).mp
  change e.hom ≫ (e.inv ≫ _) ≫ _ = e.hom ≫ _
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  exact (product_comparison L.val M.val N.val a b c).symm

end AlgebraicGeometry.Scheme.Modules.Hom
