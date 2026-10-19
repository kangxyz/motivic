/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.Contraction
public import Motivic.Aglib.CategoryTheory.SplitCokernelKernel
public import Motivic.Cohomology.A1.Basic

/-!
# The unit-section kernel description of HI contraction

For homotopy-invariant coefficients, contraction is canonically the kernel of
restriction along the actual unit section. The comparison is natural for all
signed transfers and subtracts precisely the constant component. Only ordinary
homotopy invariance is used; no strict invariance or sheafification claim occurs.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe v u

namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k]

instance base_geometricallyIntegral :
    GeometricallyIntegral (SmoothSite.base (Spec (.of k))).hom :=
  inferInstanceAs (GeometricallyIntegral (𝟙 (Spec (.of k))))

/-- Base-product sections; the literal first projection identifies them with the original values. -/
abbrev baseSections (P : PresheafWithTransfers.{v} k) : PresheafWithTransfers.{v} k :=
  withParameter P (SmoothSite.base (Spec (.of k)))

/-- The actual Laurent projection, using the literal base product. -/
def torusConstant (P : PresheafWithTransfers.{v} k) : baseSections P ⟶ torusSections P :=
  parameterPullback P (SmoothSite.toBase (.of k) (SmoothSite.torus (.of k)))

/-- The actual Laurent identity-coordinate restriction, natural for all transfers. -/
def torusUnit (P : PresheafWithTransfers.{v} k) : torusSections P ⟶ baseSections P :=
  parameterPullback P (SmoothSite.torusOne (.of k))

/-- The literal affine-line projection in base-product coordinates. -/
def affineLineConstant (P : PresheafWithTransfers.{v} k) :
    baseSections P ⟶ affineLineSections P :=
  parameterPullback P (SmoothSite.toBase (.of k) (SmoothSite.affineLine (.of k)))

@[reassoc (attr := simp)] theorem torusConstant_unit (P : PresheafWithTransfers.{v} k) :
    torusConstant P ≫ torusUnit P = 𝟙 (baseSections P) := by
  rw [torusConstant, torusUnit, ← parameterPullback_comp]
  have h : SmoothSite.torusOne (.of k) ≫
      SmoothSite.toBase (.of k) (SmoothSite.torus (.of k)) =
      𝟙 (SmoothSite.base (Spec (.of k))) := by
    rw [SmoothSite.comp_toBase]
    rfl
  rw [h, parameterPullback_id]

@[reassoc (attr := simp)] theorem affineLineConstant_restriction
    (P : PresheafWithTransfers.{v} k) :
    affineLineConstant P ≫ contractionRestriction P = torusConstant P := by
  rw [affineLineConstant, contractionRestriction, ← parameterPullback_comp,
    SmoothSite.comp_toBase]
  rfl

/-- HI applies to the genuine affine-line parameter projection. -/
theorem affineLineConstant_isIso (P : PresheafWithTransfers.{v} k) (hP : IsA1Invariant P) :
    IsIso (affineLineConstant P).hom := by
  have : ∀ X, IsIso ((affineLineConstant P).hom.app X) := by
    intro X
    let e := P.obj.mapIso ((Cor.graphFunctor k).mapIso
      (SmoothSite.productBaseIso (.of k) X.unop.toSmoothSite)).op
    have he : IsIso e.hom := inferInstance
    have h : e.hom ≫ (affineLineConstant P).hom.app X =
        A1.projectionPullback (.of k) ((toPresheaf k).obj P) X.unop.toSmoothSite := by
      change transfer P ((Cor.graphFunctor k).map (SmoothSite.productBaseIso _ _).hom) ≫
        transfer P ((Cor.graphFunctor k).map
          (SmoothSite.productMap (𝟙 _) (SmoothSite.toBase _ _))) = _
      rw [← transfer_comp, ← Functor.map_comp, SmoothSite.productMap_toBase]
      rfl
    have : IsIso (e.hom ≫ (affineLineConstant P).hom.app X) := by
      rw [h]
      exact hP X.unop.toSmoothSite
    exact IsIso.of_isIso_comp_left e.hom _
  exact NatIso.isIso_of_isIso_app _

/-- The actual unit-section kernel, with the transfers inherited by its genuine kernel. -/
def contractionKernel (P : PresheafWithTransfers.{v} k) : PresheafWithTransfers.{v} k :=
  ⟨kernel (torusUnit P).hom, ⟨by
    intro X Y f g
    apply (cancel_mono ((kernel.ι (torusUnit P).hom).app Y)).mp
    rw [Preadditive.add_comp, (kernel.ι (torusUnit P).hom).naturality,
      (kernel.ι (torusUnit P).hom).naturality,
      (kernel.ι (torusUnit P).hom).naturality, Functor.map_add,
      Preadditive.comp_add]⟩⟩

/-- The canonical isomorphism of actual transfer presheaves for HI coefficients. -/
def contractionIsoKernel (P : PresheafWithTransfers.{v} k) (hP : IsA1Invariant P) :
    contraction P ≅ contractionKernel P := by
  letI := affineLineConstant_isIso P hP
  apply ObjectProperty.isoMk
  exact ((cokernelEpiComp (affineLineConstant P).hom (contractionRestriction P).hom).symm ≪≫
      cokernelIsoOfEq (congrArg (fun f => f.hom) (affineLineConstant_restriction P)) ≪≫
      splitCokernelIsoKernel (torusConstant P).hom (torusUnit P).hom
        (congrArg (fun f => f.hom) (torusConstant_unit P)))

/-- The base-product coordinate expression is exactly the actual unit section. -/
theorem torusUnit_app_actual (P : PresheafWithTransfers.{v} k) (X : Cor k) :
    (torusUnit P).hom.app (op X) ≫
      transfer P ((Cor.graphFunctor k).map (SmoothSite.productBaseIso (.of k) X.toSmoothSite).inv) =
    transfer P ((Cor.graphFunctor k).map (SmoothSite.torusUnitSection (.of k) X.toSmoothSite)) := by
  change transfer P ((Cor.graphFunctor k).map
      (SmoothSite.productMap (𝟙 X.toSmoothSite) (SmoothSite.torusOne (.of k)))) ≫
    transfer P ((Cor.graphFunctor k).map (SmoothSite.productBaseIso (.of k) X.toSmoothSite).inv) = _
  rw [← transfer_comp, ← Functor.map_comp, SmoothSite.baseProduct_unit]

/-- Objectwise, the comparison uses precisely the kernel of the actual unit section into `X`. -/
def contractionSectionsIsoUnitKernel (P : PresheafWithTransfers.{v} k)
    (hP : IsA1Invariant P) (X : Cor k) :
    sections (contraction P) X ≅
      kernel (transfer P ((Cor.graphFunctor k).map
        (SmoothSite.torusUnitSection (.of k) X.toSmoothSite))) := by
  let e := P.obj.mapIso ((Cor.graphFunctor k).mapIso
    (SmoothSite.productBaseIso (.of k) X.toSmoothSite)).symm.op
  exact ((evaluation (Cor k)ᵒᵖ AddCommGrpCat).obj (op X)).mapIso
      (forget.mapIso (contractionIsoKernel P hP)) ≪≫
    PreservesKernel.iso ((evaluation (Cor k)ᵒᵖ AddCommGrpCat).obj (op X))
      (torusUnit P).hom ≪≫
    (kernelCompMono ((torusUnit P).hom.app (op X)) e.hom).symm ≪≫
    kernelIsoOfEq (torusUnit_app_actual P X)

/-- The kernel inclusion followed by quotient is the inverse comparison. -/
@[reassoc] theorem contractionIsoKernel_inv_quotient
    (P : PresheafWithTransfers.{v} k) (hP : IsA1Invariant P) :
    (contractionIsoKernel P hP).inv.hom =
      kernel.ι (torusUnit P).hom ≫ (toContraction P).hom := by
  simp [contractionIsoKernel, splitCokernelIsoKernel, toContraction,
    Category.assoc]

/-- The forward comparison subtracts exactly the split constant component. -/
@[reassoc] theorem contractionIsoKernel_hom_projection
    (P : PresheafWithTransfers.{v} k) (hP : IsA1Invariant P) :
    (toContraction P).hom ≫ (contractionIsoKernel P hP).hom.hom ≫
        kernel.ι (torusUnit P).hom =
      𝟙 (torusSections P).obj - (torusUnit P).hom ≫ (torusConstant P).hom := by
  simp [contractionIsoKernel, splitCokernelIsoKernel, toContraction, Category.assoc]

/-- The actual constant and contraction summands add to the identity. -/
theorem contraction_split_identity
    (P : PresheafWithTransfers.{v} k) (hP : IsA1Invariant P) :
    (torusUnit P).hom ≫ (torusConstant P).hom +
      (toContraction P).hom ≫ (contractionIsoKernel P hP).hom.hom ≫
        kernel.ι (torusUnit P).hom = 𝟙 (torusSections P).obj := by
  rw [contractionIsoKernel_hom_projection]
  rw [add_comm, sub_add_cancel]

end Motivic.PresheafWithTransfers
