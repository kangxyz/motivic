/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Sheaf.Germs.Tuples.Transfers
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Germs.SectionDetection

/-!
# Germ tuples for presheaves with transfers
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Opposite AlgebraicGeometry
universe u
namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme
variable (k : Type u) [Field k] (P : PresheafWithTransfers.{u + 1} k)
  (hP : Presheaf.IsSheaf (SmoothSite.nisnevichTopology (Spec (.of k))) ((toPresheaf k).obj P))

/-- The actual transfer-natural map to original germ tuples is objectwise injective. -/
theorem toOriginalGermTuplePresheaf_injective (X : Cor k) :
    Function.Injective ((toOriginalGermTuplePresheaf k P hP).hom.app (op X)) :=
  SmoothSite.original_germ_tuple_injective ((toPresheaf k).obj P) hP X.toSmoothSite

end Motivic.PresheafWithTransfers
