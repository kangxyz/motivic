/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.Boundary.RestrictionDifference.Restriction

/-! # Transport of the actual ambient correction through a geometric isomorphism -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

/-- Only the correction section is transported; the original presheaf, original
section, and minus sign remain unchanged under the actual ambient isomorphism. -/
theorem HasRestrictionDifferenceLifting.iso_ambient
    {k : Type u} [Field k] (P : PresheafWithTransfers.{u + 1} k)
    {O D T T' A : SmoothSite (Spec (.of k))}
    {φ : O ⟶ D} {β : O ⟶ A} {α : O ⟶ T}
    (h : P.HasRestrictionDifferenceLifting φ β α) (e : T ≅ T') :
    P.HasRestrictionDifferenceLifting φ β (α ≫ e.hom) := by
  intro d
  let F := (toPresheaf k).obj P
  obtain ⟨a, c, hac⟩ := h d
  refine ⟨a, F.map e.inv.op c, ?_⟩
  change F.map β.op a - F.map (α ≫ e.hom).op (F.map e.inv.op c) = F.map φ.op d
  rw [← ConcreteCategory.comp_apply, ← F.map_comp, ← op_comp,
    Category.assoc, e.hom_inv_id, Category.comp_id]
  exact hac

end Motivic.PresheafWithTransfers
