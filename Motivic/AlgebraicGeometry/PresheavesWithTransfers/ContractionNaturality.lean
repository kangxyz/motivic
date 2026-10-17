/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.PresheavesWithTransfers.ContractionHI

/-!
# Coefficient naturality of contraction and its HI splitting

Both quotient and kernel maps are induced by the actual parameter evaluations.
The canonical HI comparison commutes with all coefficient morphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe v u

namespace Motivic.PresheafWithTransfers

variable {k : Type u} [Field k]

/-- Maps out of contraction are determined by their genuine Laurent representatives. -/
theorem contraction_hom_ext (P : PresheafWithTransfers.{v} k)
    {Q : PresheafWithTransfers.{v} k} {η θ : contraction P ⟶ Q}
    (h : toContraction P ≫ η = toContraction P ≫ θ) : η = θ := by
  apply ObjectProperty.hom_ext
  apply (cancel_epi (cokernel.π (contractionRestriction P).hom)).mp
  exact congrArg (fun f => f.hom) h

@[simp] theorem contractionMap_id (P : PresheafWithTransfers.{v} k) :
    contractionMap (𝟙 P) = 𝟙 (contraction P) := by
  apply contraction_hom_ext
  rw [toContraction_map, Category.comp_id]
  change 𝟙 (torusSections P) ≫ toContraction P = toContraction P
  exact Category.id_comp _

@[simp] theorem contractionMap_comp {P Q R : PresheafWithTransfers.{v} k}
    (η : P ⟶ Q) (θ : Q ⟶ R) :
    contractionMap (η ≫ θ) = contractionMap η ≫ contractionMap θ := by
  apply contraction_hom_ext
  rw [toContraction_map, ← Category.assoc, toContraction_map,
    Category.assoc, toContraction_map]
  change (withParameterMap η (SmoothSite.torus (.of k)) ≫
      withParameterMap θ (SmoothSite.torus (.of k))) ≫ toContraction R = _
  exact Category.assoc _ _ _

/-- Contraction is functorial in the actual coefficient presheaf. -/
def contractionFunctor (k : Type u) [Field k] :
    PresheafWithTransfers.{v} k ⥤ PresheafWithTransfers.{v} k where
  obj := contraction
  map := contractionMap
  map_id := contractionMap_id
  map_comp := contractionMap_comp

/-- The kernel map is induced by the two actual parameter evaluations. -/
def contractionKernelMap {P Q : PresheafWithTransfers.{v} k} (η : P ⟶ Q) :
    contractionKernel P ⟶ contractionKernel Q :=
  ⟨kernel.map (torusUnit P).hom (torusUnit Q).hom
    (withParameterMap η (SmoothSite.torus (.of k))).hom
    (withParameterMap η (SmoothSite.base (Spec (.of k)))).hom
    (congrArg (fun f => f.hom)
      (parameterPullback_coefficient_naturality η (SmoothSite.torusOne (.of k))))⟩

/-- The inverse HI comparison, which is inclusion followed by quotient, is coefficient-natural. -/
@[reassoc] theorem contractionIsoKernel_inv_naturality
    {P Q : PresheafWithTransfers.{v} k} (η : P ⟶ Q)
    (hP : IsA1Invariant P) (hQ : IsA1Invariant Q) :
    contractionKernelMap η ≫ (contractionIsoKernel Q hQ).inv =
      (contractionIsoKernel P hP).inv ≫ contractionMap η := by
  apply ObjectProperty.hom_ext
  change (contractionKernelMap η).hom ≫ (contractionIsoKernel Q hQ).inv.hom =
    (contractionIsoKernel P hP).inv.hom ≫ (contractionMap η).hom
  rw [contractionIsoKernel_inv_quotient, contractionIsoKernel_inv_quotient]
  change kernel.map (torusUnit P).hom (torusUnit Q).hom
      (withParameterMap η (SmoothSite.torus (.of k))).hom
      (withParameterMap η (SmoothSite.base (Spec (.of k)))).hom
      (congrArg (fun f => f.hom)
        (parameterPullback_coefficient_naturality η (SmoothSite.torusOne (.of k)))) ≫
    (kernel.ι (torusUnit Q).hom ≫ _) = (kernel.ι (torusUnit P).hom ≫ _) ≫ _
  rw [← Category.assoc, kernel.lift_ι, Category.assoc, Category.assoc]
  exact congrArg (fun f => kernel.ι (torusUnit P).hom ≫ f.hom)
    (toContraction_map η).symm

/-- The canonical kernel description is also natural in the coefficient presheaf. -/
@[reassoc] theorem contractionIsoKernel_hom_naturality
    {P Q : PresheafWithTransfers.{v} k} (η : P ⟶ Q)
    (hP : IsA1Invariant P) (hQ : IsA1Invariant Q) :
    contractionMap η ≫ (contractionIsoKernel Q hQ).hom =
      (contractionIsoKernel P hP).hom ≫ contractionKernelMap η := by
  apply (cancel_epi (contractionIsoKernel P hP).inv).mp
  rw [← Category.assoc, ← contractionIsoKernel_inv_naturality η hP hQ,
    Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]

end Motivic.PresheafWithTransfers
