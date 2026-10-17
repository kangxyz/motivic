/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.DerivedCategory.AdjunctionExtEdgeWindow

/-! # Endpoint-free injectivity of the original Ext adjunction edge -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe w₁ w₂ w₃ w₄ v₁ v₂ u₁ u₂
namespace CategoryTheory.Adjunction
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
  [HasExt.{w₃} C] [HasExt.{w₄} D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L] (adj : L ⊣ R)
  {Y : D} {P : C} (N : ℕ)

variable [PreservesFiniteLimits R] [HasInjectiveResolutions D]
  (I : InjectiveResolution Y)
include I

/-- Injectivity of the original Ext edge does not require vanishing at the endpoint. -/
theorem extEdge_injective_of_rightDerived_window
    (hR : ∀ q : ℕ, 0 < q → q < N → IsZero ((R.rightDerived q).obj Y)) :
    Function.Injective (adj.extEdge (P := P) (Y := Y) N) := by
  have h₀ : Function.Injective
      (fun x : (DerivedCategory.singleFunctor C (N : ℤ)).obj P ⟶
        (DerivedCategory.singleFunctor C 0).obj (R.obj Y) =>
          L.mapDerivedCategory.map x ≫ adj.imageEdgeCounit Y) := by
    intro x y hxy
    apply adj.derivedImageEdge_injective I P N hR
    simpa only [adj.derivedImageEdge_eq] using
      congrArg (L.mapDerivedCategoryFactors.inv.app
        ((CochainComplex.singleFunctor C (N : ℤ)).obj P) ≫ ·) hxy
  have h₁ := L.mapDerivedCategory.map_postcomp_shift_injective
    (adj.imageEdgeCounit Y) (N : ℤ) h₀
  have h₂ := L.mapDerivedCategory.map_postcomp_isoSource_injective _
    (((DerivedCategory.singleFunctors C).shiftIso (N : ℤ) 0 N (add_zero _)).app P) h₁
  intro x y hxy
  apply Ext.homEquiv.injective
  apply h₂
  apply (cancel_epi ((L.mapDerivedCategorySingleFunctor 0).inv.app P)).mp
  simpa only [adj.extEdge_hom_formula] using congrArg Ext.hom hxy

end CategoryTheory.Adjunction
