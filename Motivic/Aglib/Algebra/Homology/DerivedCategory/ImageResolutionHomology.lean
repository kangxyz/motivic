/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.DerivedCategory.ImageResolution

/-! # Degree-zero exactness of the actual image-resolution augmentation -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe v₁ v₂ u₁ u₂
namespace CategoryTheory.InjectiveResolution
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] {Y : C} (I : InjectiveResolution Y)
  (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R]

/-- Left exactness supplies degree-zero exactness of the actual augmentation. -/
instance imageι_quasiIsoAt_zero : QuasiIsoAt (I.imageι R) 0 := by
  rw [CochainComplex.quasiIsoAt₀_iff]
  rw [ShortComplex.quasiIso_iff_of_zeros _ (by simp) (by simp) (by simp)]
  change (ShortComplex.mk ((I.imageι R).f 0) (R.map (I.cocomplex.d 0 1)) _).Exact ∧
    Mono ((I.imageι R).f 0)
  simp only [imageι_f_zero]
  rw [ShortComplex.exact_and_mono_f_iff_f_is_kernel]
  exact ⟨KernelFork.mapIsLimit _ I.isLimitKernelFork R⟩

/-- Extending the actual augmentation by zero retains its degree-zero quasi-isomorphism. -/
instance imageExtendedι_quasiIsoAt_zero : QuasiIsoAt (I.imageExtendedι R) 0 := by
  have : QuasiIsoAt (extendMap (I.imageι R) ComplexShape.embeddingUpNat) (0 : ℤ) :=
    (quasiIsoAt_extendMap_iff (I.imageι R) ComplexShape.embeddingUpNat
      (j := 0) (hj' := rfl)).mpr inferInstance
  dsimp only [imageExtendedι]
  infer_instance

end CategoryTheory.InjectiveResolution
