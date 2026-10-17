/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.DerivedCategory.ImageFirstObstruction
public import Motivic.Aglib.Algebra.Homology.DerivedCategory.ImageResolutionExtCoordinates

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

/-- The actual right-derived-image obstruction of an original Ext class. -/
def extFirstObstruction (x : Ext (L.obj P) Y N) : P ⟶ (R.rightDerived N).obj Y :=
  I.imageFirstObstruction R P N ((adj.imageResolutionExtAddEquiv I P N).symm x)

/-- The first obstruction detects precisely the image of the original adjunction edge.
Only lower positive right-derived images vanish; no surjectivity of the obstruction is claimed. -/
theorem extFirstObstruction_eq_zero_iff (hN : 0 < N)
    (hR : ∀ q : ℕ, 0 < q → q < N → IsZero ((R.rightDerived q).obj Y))
    (x : Ext (L.obj P) Y N) :
    adj.extFirstObstruction I P N x = 0 ↔
      ∃ z : Ext P (R.obj Y) N, adj.extEdge N z = x := by
  rw [extFirstObstruction, I.imageFirstObstruction_eq_zero_iff R P N hN hR]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨imageSourceExtAddEquiv (R := R) P N g, ?_⟩
    rw [← adj.imageResolutionExtAddEquiv_augmentation I P N, hg]
    exact (adj.imageResolutionExtAddEquiv I P N).apply_symm_apply x
  · rintro ⟨z, rfl⟩
    refine ⟨(imageSourceExtAddEquiv (R := R) P N).symm z, ?_⟩
    apply (adj.imageResolutionExtAddEquiv I P N).injective
    rw [adj.imageResolutionExtAddEquiv_augmentation]
    simp only [AddEquiv.apply_symm_apply]

end CategoryTheory.Adjunction
