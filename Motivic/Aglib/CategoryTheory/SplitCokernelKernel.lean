/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Canonical cokernel-to-kernel comparison for a split pair

The forward map subtracts the actual split constant part; its inverse is the
kernel inclusion followed by the actual quotient. This elementary comparison
uses no homotopy invariance or strict-invariance theorem.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {A B : C} (i : A ⟶ B) (p : B ⟶ A) (h : i ≫ p = 𝟙 A)
  [HasKernel p]

/-- Remove the actual constant component of a split pair. -/
def splitKernelProjection : B ⟶ kernel p :=
  kernel.lift p (𝟙 B - p ≫ i) (by
    simp only [Preadditive.sub_comp, Category.id_comp, Category.assoc, h,
      Category.comp_id, sub_self])

@[reassoc (attr := simp)] theorem splitKernelProjection_ι :
    splitKernelProjection i p h ≫ kernel.ι p = 𝟙 B - p ≫ i :=
  kernel.lift_ι _ _ _

@[reassoc (attr := simp)] theorem comp_splitKernelProjection :
    i ≫ splitKernelProjection i p h = 0 := by
  apply (cancel_mono (kernel.ι p)).mp
  rw [Category.assoc, splitKernelProjection_ι, Preadditive.comp_sub,
    Category.comp_id, ← Category.assoc, h, Category.id_comp, sub_self, zero_comp]

variable [HasCokernel i]

/-- The canonical split cokernel is the kernel of the actual retraction. -/
def splitCokernelIsoKernel : cokernel i ≅ kernel p where
  hom := cokernel.desc i (splitKernelProjection i p h) (comp_splitKernelProjection i p h)
  inv := kernel.ι p ≫ cokernel.π i
  hom_inv_id := by
    apply (cancel_epi (cokernel.π i)).mp
    simp only [cokernel.π_desc_assoc, Category.comp_id]
    rw [← Category.assoc, splitKernelProjection_ι]
    simp only [Preadditive.sub_comp, Category.id_comp, Category.assoc,
      cokernel.condition, comp_zero, sub_zero]
  inv_hom_id := by
    apply (cancel_mono (kernel.ι p)).mp
    simp only [Category.assoc, cokernel.π_desc_assoc, splitKernelProjection_ι,
      Category.id_comp]
    simp only [Preadditive.comp_sub, Category.comp_id, ← Category.assoc,
      kernel.condition, zero_comp, sub_zero]

@[reassoc (attr := simp)] theorem splitCokernelIsoKernel_hom_ι :
    cokernel.π i ≫ (splitCokernelIsoKernel i p h).hom ≫ kernel.ι p =
      𝟙 B - p ≫ i := by
  simp [splitCokernelIsoKernel]

@[simp] theorem splitCokernelIsoKernel_inv :
    (splitCokernelIsoKernel i p h).inv = kernel.ι p ≫ cokernel.π i := rfl

end CategoryTheory
