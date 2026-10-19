/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.Representable
public import Motivic.AlgebraicGeometry.Correspondences.Graph.Functor

/-!
# The underlying ordinary presheaf of a presheaf with transfers

Restriction along the proved actual graph functor sends a presheaf with
transfers to an ordinary abelian presheaf on the smooth site. Ordinary
restriction is the transfer along the actual componentwise graph cycle.
The restriction functor is additive and faithful, and its output can be used
directly by the project's existing ordinary presheaf constructions.

No topology or transfer-preserving sheafification is asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe v u

namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k]

/-- Forget transfers by restricting along the actual componentwise graph functor. -/
def toPresheaf : PresheafWithTransfers.{v} k ⥤
    (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{v} :=
  restrictAlong (Cor.graphFunctor k)

instance : (toPresheaf.{v} k).Additive := by
  dsimp [toPresheaf]
  infer_instance

instance : (toPresheaf.{v} k).Faithful where
  map_injective {P Q η θ} h := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    exact congrArg (fun f => f.app (op X.unop.toSmoothSite)) h

@[simp]
theorem toPresheaf_obj_obj (P : PresheafWithTransfers.{v} k)
    (X : (SmoothSite (Spec (.of k)))ᵒᵖ) :
    ((toPresheaf k).obj P).obj X = sections P (Cor.mk X.unop) := rfl

/-- An ordinary restriction map is transfer along the proved graph functor. -/
@[simp]
theorem toPresheaf_obj_map (P : PresheafWithTransfers.{v} k)
    {X Y : (SmoothSite (Spec (.of k)))ᵒᵖ} (f : X ⟶ Y) :
    ((toPresheaf k).obj P).map f = transfer P ((Cor.graphFunctor k).map f.unop) := rfl

@[simp]
theorem toPresheaf_map_app {P Q : PresheafWithTransfers.{v} k} (η : P ⟶ Q)
    (X : (SmoothSite (Spec (.of k)))ᵒᵖ) :
    ((toPresheaf k).map η).app X = η.hom.app (op (Cor.mk X.unop)) := rfl

/-- The underlying presheaf of a representable retains the actual correspondence groups. -/
@[simp]
theorem toPresheaf_representable_obj (X : Cor k) (Y : SmoothSite (Spec (.of k))) :
    ((toPresheaf k).obj ((representable k).obj X)).obj (op Y) =
      AddCommGrpCat.of (FiniteCorrespondence Y.hom X.toSmoothSite.hom) := rfl

/-- Ordinary restriction on a representable is precomposition by the actual graph cycle. -/
@[simp]
theorem toPresheaf_representable_map_apply (X : Cor k)
    {Y Z : SmoothSite (Spec (.of k))} (f : Y ⟶ Z) (α : Cor.mk Z ⟶ X) :
    ((toPresheaf k).obj ((representable k).obj X)).map f.op α =
      (Cor.graphFunctor k).map f ≫ α := rfl

end Motivic.PresheafWithTransfers
