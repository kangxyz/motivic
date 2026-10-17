/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.SmoothSiteBaseChangeProducts

/-! # Consumers of actual relative product comparisons under arbitrary base change -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic Motivic.SmoothSite

universe u

namespace MotivicTest.SmoothSiteBaseChangeProducts

variable {S T : Scheme.{u}} (f : T ⟶ S) (X Y : SmoothSite S)

example : (baseChangeBaseIso f).hom.left = pullback.snd (𝟙 S) f := rfl

example : ((baseChange f).obj (product X Y)).left =
    pullback (pullback.fst X.hom Y.hom ≫ X.hom) f := rfl

example : (baseChangeProductIso f X Y).hom ≫
    productFst ((baseChange f).obj X) ((baseChange f).obj Y) =
      (baseChange f).map (productFst X Y) := by simp

example : (baseChangeProductIso f X Y).hom ≫
    productSnd ((baseChange f).obj X) ((baseChange f).obj Y) =
      (baseChange f).map (productSnd X Y) := by simp

example : (baseChangeProductIso f X Y).inv ≫ (baseChange f).map (productFst X Y) =
    productFst ((baseChange f).obj X) ((baseChange f).obj Y) := by simp

example : (baseChangeProductIso f X Y).inv ≫ (baseChange f).map (productSnd X Y) =
    productSnd ((baseChange f).obj X) ((baseChange f).obj Y) := by simp

example {X' Y' : SmoothSite S} (a : X ≅ X') (b : Y ≅ Y') :
    (productIso a b).hom = productMap a.hom b.hom := rfl

example {X' Y' : SmoothSite S} (a : X ≅ X') (b : Y ≅ Y') :
    (productIso a b).inv = productMap a.inv b.inv := rfl

example {X' Y' : SmoothSite S} (a : X ≅ X') (b : Y ≅ Y') :
    (productIso a b).hom ≫ productFst X' Y' = productFst X Y ≫ a.hom := by simp

example {X' Y' : SmoothSite S} (a : X ≅ X') (b : Y ≅ Y') :
    (productIso a b).hom ≫ productSnd X' Y' = productSnd X Y ≫ b.hom := by simp

set_option linter.hashCommand false in
#print axioms Motivic.SmoothSite.baseChangeBaseIso
set_option linter.hashCommand false in
#print axioms Motivic.SmoothSite.baseChangeProductIso
set_option linter.hashCommand false in
#print axioms Motivic.SmoothSite.productIso

end MotivicTest.SmoothSiteBaseChangeProducts
