/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.PresheavesWithTransfers.Basic
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# Representable presheaves with transfers

The additive Yoneda presheaf represented by `X : Cor k` sends `Y` to the actual
abelian group of signed finite correspondences from `Y` to `X`. Its transfer
maps are precomposition by the incidence Tor pairing. Postcomposition gives
a fully faithful additive functor from actual correspondences to presheaves
with transfers. This construction uses the existing preadditive Yoneda API;
there is no free replacement of the correspondence groups.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace Motivic.PresheafWithTransfers

variable (k : Type u) [Field k]

/-- The representable presheaf-with-transfers embedding of actual correspondences. -/
def representable : Cor k ⥤ PresheafWithTransfers.{u} k :=
  (additiveFunctor _ _).lift preadditiveYoneda (fun X => by
    change (preadditiveYoneda.obj X).Additive
    infer_instance)

instance : (representable k).Full := by
  dsimp [representable]
  infer_instance

instance : (representable k).Faithful := by
  dsimp [representable]
  infer_instance

instance : (representable k).Additive where
  map_add {X Y α β} := by
    apply ObjectProperty.hom_ext
    ext Z γ
    exact Preadditive.comp_add Z.unop X Y γ α β

/-- The value of a representable is literally the group of actual signed cycles. -/
@[simp]
theorem representable_sections (X Y : Cor k) :
    sections ((representable k).obj X) Y =
      AddCommGrpCat.of (FiniteCorrespondence Y.toSmoothSite.hom X.toSmoothSite.hom) := rfl

/-- Transfer on a representable is actual incidence Tor precomposition. -/
@[simp]
theorem representable_transfer_apply {X Y Z : Cor k} (α : Y ⟶ Z) (β : Z ⟶ X) :
    transfer ((representable k).obj X) α β = α ≫ β := rfl

/-- The representing-object functor acts by actual incidence Tor postcomposition. -/
@[simp]
theorem representable_map_app_apply {X Y Z : Cor k} (α : X ⟶ Y) (β : Z ⟶ X) :
    ((representable k).map α).hom.app (op Z) β = β ≫ α := rfl

/-- Forgetting the bundled additivity gives Mathlib's preadditive Yoneda functor. -/
theorem representable_comp_forget : representable k ⋙ forget = preadditiveYoneda := rfl

end Motivic.PresheafWithTransfers
