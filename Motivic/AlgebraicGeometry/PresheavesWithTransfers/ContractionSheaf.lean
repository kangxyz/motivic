/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.SmoothSiteParameterProducts
public import Motivic.AlgebraicGeometry.PresheavesWithTransfers.ContractionInvariance
public import Motivic.AlgebraicGeometry.PresheavesWithTransfers.Limits

/-!
# Actual contraction of homotopy-invariant Nisnevich sheaves

Parameter products preserve the ordinary Nisnevich sheaf condition. Their
graph restrictions are exactly the actual smooth-site product pullbacks.
For already homotopy-invariant Nisnevich sheaves with transfers, the existing
natural unit-section kernel description therefore proves that the literal
presheaf contraction is a Nisnevich sheaf with transfers. Its ordinary
homotopy invariance is the existing contraction theorem.

The original coefficient universe and signed transfer action are unchanged.
This is not a comparison between contraction and sheafification of a general
homotopy-invariant presheaf, and it asserts no positive-degree strict invariance.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe v u

namespace Motivic.PresheafWithTransfers

variable {k : Type u} [Field k]

set_option backward.isDefEq.respectTransparency false in
/-- Graph restriction of actual parameter transfers is ordinary restriction on
the same literal smooth-site products. -/
def withParameterUnderlyingIso (P : PresheafWithTransfers.{v} k)
    (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom] :
    (toPresheaf k).obj (withParameter P T) ≅
      (SmoothSite.parameterProduct T).op ⋙ (toPresheaf k).obj P :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by
    change transfer P ((Cor.parameterProduct T).map ((Cor.graphFunctor k).map f.unop)) ≫
        𝟙 _ = 𝟙 _ ≫
      transfer P ((Cor.graphFunctor k).map (SmoothSite.productMap f.unop (𝟙 T)))
    rw [Category.comp_id, Category.id_comp, Cor.parameterProduct_graph])

/-- Nisnevich sheafness survives actual smooth parameter products; HI is not needed here. -/
theorem withParameter_isNisnevichSheaf (P : PresheafWithTransfers.{v} k)
    (hP : IsNisnevichSheaf k P) (T : SmoothSite (Spec (.of k)))
    [GeometricallyIntegral T.hom] : IsNisnevichSheaf k (withParameter P T) := by
  apply (Presheaf.isSheaf_of_iso_iff (withParameterUnderlyingIso P T)).mpr
  exact (SmoothSite.parameterProduct T).op_comp_isSheaf_of_isSheaf _ _ _ hP

/-- The underlying ordinary presheaf of the actual unit-section kernel is the
ordinary kernel of the same graph-restricted unit-section map. -/
def contractionKernelUnderlyingIso (P : PresheafWithTransfers.{v} k) :
    (toPresheaf k).obj (contractionKernel P) ≅
      kernel ((toPresheaf k).map (torusUnit P)) :=
  PreservesKernel.iso ((Functor.whiskeringLeft _ _ AddCommGrpCat.{v}).obj
    (Cor.graphFunctor k).op) (torusUnit P).hom

/-- The unit-section kernel of Nisnevich coefficients is a genuine Nisnevich sheaf. -/
theorem contractionKernel_isNisnevichSheaf (P : PresheafWithTransfers.{v} k)
    (hP : IsNisnevichSheaf k P) : IsNisnevichSheaf k (contractionKernel P) := by
  apply (Presheaf.isSheaf_of_iso_iff (contractionKernelUnderlyingIso P)).mpr
  apply ObjectProperty.prop_limit
    (Presheaf.IsSheaf (SmoothSite.nisnevichTopology (Spec (.of k))) (A := AddCommGrpCat.{v}))
    (parallelPair ((toPresheaf k).map (torusUnit P)) 0)
  intro j
  cases j with
  | zero => exact withParameter_isNisnevichSheaf P hP (SmoothSite.torus (.of k))
  | one => exact withParameter_isNisnevichSheaf P hP (SmoothSite.base (Spec (.of k)))

/-- The literal contraction of already HI Nisnevich coefficients is itself Nisnevich. -/
theorem contraction_isNisnevichSheaf (P : PresheafWithTransfers.{v} k)
    (hP : IsNisnevichSheaf k P) (hHI : IsA1Invariant P) :
    IsNisnevichSheaf k (contraction P) :=
  (Presheaf.isSheaf_of_iso_iff
    ((toPresheaf k).mapIso (contractionIsoKernel P hHI))).mpr
      (contractionKernel_isNisnevichSheaf P hP)

end Motivic.PresheafWithTransfers

namespace Motivic.SheafWithTransfers

variable {k : Type u} [Field k]

/-- Contraction of an HI sheaf with transfers, retaining the literal presheaf contraction. -/
def contraction (F : SheafWithTransfers.{v} k) (hF : F.obj.IsA1Invariant) :
    SheafWithTransfers.{v} k :=
  ⟨PresheafWithTransfers.contraction F.obj,
    PresheafWithTransfers.contraction_isNisnevichSheaf F.obj F.property hF⟩

@[simp]
theorem contraction_obj (F : SheafWithTransfers.{v} k) (hF : F.obj.IsA1Invariant) :
    (contraction F hF).obj = PresheafWithTransfers.contraction F.obj := rfl

/-- This actual contraction is again ordinarily homotopy invariant. -/
theorem contraction_isA1Invariant (F : SheafWithTransfers.{v} k)
    (hF : F.obj.IsA1Invariant) : (contraction F hF).obj.IsA1Invariant :=
  PresheafWithTransfers.contraction_isA1Invariant F.obj hF

end Motivic.SheafWithTransfers
