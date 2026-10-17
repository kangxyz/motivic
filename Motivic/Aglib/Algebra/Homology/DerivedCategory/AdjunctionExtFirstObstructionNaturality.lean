/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.DerivedCategory.AdjunctionExtFirstObstruction
public import Motivic.Aglib.Algebra.Homology.DerivedCategory.ImageResolutionExtNaturality

/-! # First right-derived obstruction for the original Ext edge -/
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
  [PreservesFiniteLimits L] [PreservesFiniteColimits L] [PreservesFiniteLimits R]
  [HasInjectiveResolutions D] (adj : L ⊣ R)
  {Y : D} (I : InjectiveResolution Y) (P : C) (N : ℕ)

omit [HasExt C] [PreservesFiniteLimits R] in
/-- The actual first obstruction respects original Ext source restriction. -/
theorem extFirstObstruction_naturality {P' : C} (a : P' ⟶ P)
    (x : Ext (L.obj P) Y N) :
    adj.extFirstObstruction I P' N ((Ext.mk₀ (L.map a)).comp x (zero_add N)) =
      a ≫ adj.extFirstObstruction I P N x := by
  let f := (adj.imageResolutionExtAddEquiv I P N).symm x
  have hf : (adj.imageResolutionExtAddEquiv I P' N).symm
      ((Ext.mk₀ (L.map a)).comp x (zero_add N)) =
        (DerivedCategory.singleFunctor C (N : ℤ)).map a ≫ f := by
    apply (adj.imageResolutionExtAddEquiv I P' N).injective
    rw [AddEquiv.apply_symm_apply, adj.imageResolutionExtAddEquiv_naturality]
    simp only [f, AddEquiv.apply_symm_apply]
  simp only [extFirstObstruction, hf]
  exact I.imageFirstObstruction_naturality R P N a f

end CategoryTheory.Adjunction
