/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.A1.Basic
public import Motivic.AlgebraicGeometry.Correspondences.Moving.OneSided.MovingEndpoints
/-! # The moving homotopy acts on arbitrary HI presheaves with transfers -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
universe v u
namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme
variable {k : Type u} [Field k]

/-- This is an ordinary presheaf statement, with no Nisnevich sheaf condition. -/
theorem restriction_factor_of_moving_endpoints
    (P : PresheafWithTransfers.{v} k) (hP : P.IsA1Invariant)
    {S X V : SmoothSite (Spec (.of k))} (φ : S ⟶ X) (v : V ⟶ X)
    (β : Cor.mk S ⟶ Cor.mk V)
    (α : Cor.mk (SmoothSite.a1Cylinder (.of k) S) ⟶ Cor.mk X)
    (h0 : (Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) S 0) ≫ α =
      (Cor.graphFunctor k).map φ)
    (h1 : (Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) S 1) ≫ α =
      β ≫ (Cor.graphFunctor k).map v) :
    P.transfer ((Cor.graphFunctor k).map φ) =
      P.transfer ((Cor.graphFunctor k).map v) ≫ P.transfer β := by
  have h := transfer_homotopy_endpoints P hP S (Cor.mk X) α 0 1
  erw [h0, h1, transfer_comp] at h
  exact h

/-- A section vanishing on the original dense open vanishes on the actual moving
parameter neighborhood. Density is used by the geometric presentation, not here. -/
theorem section_zero_of_moving_endpoints
    (P : PresheafWithTransfers.{v} k) (hP : P.IsA1Invariant)
    {S X V : SmoothSite (Spec (.of k))} (φ : S ⟶ X) (v : V ⟶ X)
    (β : Cor.mk S ⟶ Cor.mk V)
    (α : Cor.mk (SmoothSite.a1Cylinder (.of k) S) ⟶ Cor.mk X)
    (h0 : (Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) S 0) ≫ α =
      (Cor.graphFunctor k).map φ)
    (h1 : (Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) S 1) ≫ α =
      β ≫ (Cor.graphFunctor k).map v)
    (s : P.sections (Cor.mk X))
    (hs : P.transfer ((Cor.graphFunctor k).map v) s = 0) :
    P.transfer ((Cor.graphFunctor k).map φ) s = 0 := by
  have h := ConcreteCategory.congr_hom
    (restriction_factor_of_moving_endpoints P hP φ v β α h0 h1) s
  change P.transfer ((Cor.graphFunctor k).map φ) s =
    P.transfer β (P.transfer ((Cor.graphFunctor k).map v) s) at h
  erw [hs, map_zero] at h
  exact h

end Motivic.PresheafWithTransfers
