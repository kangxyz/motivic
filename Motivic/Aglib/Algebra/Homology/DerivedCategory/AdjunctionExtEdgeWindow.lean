/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.DerivedCategory.AdjunctionShiftedEdgeWindow
public import Motivic.Aglib.Algebra.Homology.DerivedCategory.AdjunctionEdgeMap

/-! # Finite-window bijectivity of the original Ext adjunction edge -/
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

omit [R.Additive] in
/-- Recognition in original Ext coordinates uses the original exact-functor map and counit. -/
theorem extEdge_hom_formula (x : Ext P (R.obj Y) N) :
    (adj.extEdge N x).hom =
      (L.mapDerivedCategorySingleFunctor 0).inv.app P ≫
        L.mapDerivedCategory.map x.hom ≫
          (L.mapDerivedCategory.commShiftIso (N : ℤ)).hom.app
            ((DerivedCategory.singleFunctor C 0).obj (R.obj Y)) ≫
              (adj.imageEdgeCounit Y)⟦(N : ℤ)⟧' := by
  simp [extEdge, Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.comp_mk₀,
    Ext.mapExactFunctor_hom, ShiftedHom.map, imageEdgeCounit, Functor.map_comp, Category.assoc]

variable [PreservesFiniteLimits R] [HasInjectiveResolutions D]
  (I : InjectiveResolution Y)
include I

/-- Only the genuine finite positive right-derived vanishing window is assumed. -/
theorem extEdge_bijective_of_rightDerived_window
    (hR : ∀ q : ℕ, 0 < q → q ≤ N → IsZero ((R.rightDerived q).obj Y)) :
    Function.Bijective (adj.extEdge (P := P) (Y := Y) N) := by
  have h := adj.shiftedImageEdge_bijective I P N hR
  constructor
  · intro x y hxy
    apply Ext.homEquiv.injective
    apply h.1
    apply (cancel_epi ((L.mapDerivedCategorySingleFunctor 0).inv.app P)).mp
    simpa only [adj.extEdge_hom_formula] using congrArg Ext.hom hxy
  · intro y
    obtain ⟨x, hx⟩ := h.2 ((L.mapDerivedCategorySingleFunctor 0).hom.app P ≫ y.hom)
    refine ⟨Ext.homEquiv.symm x, ?_⟩
    apply Ext.homEquiv.injective
    change (adj.extEdge N (Ext.homEquiv.symm x)).hom = y.hom
    rw [adj.extEdge_hom_formula]
    change (L.mapDerivedCategorySingleFunctor 0).inv.app P ≫ _ = y.hom
    have hx' : (Ext.homEquiv.symm x).hom = x := Ext.homEquiv.apply_symm_apply x
    rw [hx']
    dsimp only at hx
    rw [hx]
    simp

end CategoryTheory.Adjunction
