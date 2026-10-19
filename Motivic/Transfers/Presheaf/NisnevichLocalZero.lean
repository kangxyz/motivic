/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.NisnevichSheafification
public import Motivic.Aglib.CategoryTheory.Sites.SheafifyLocallyZero

/-! # Locally zero transfer presheaves have zero genuine Nisnevich sheafification

Local vanishing is stated on the original graph restriction. The conclusion uses
the canonical comparison with ordinary sheafification and retains all transfers.
No objectwise vanishing of the original presheaf is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped ZeroObject

universe u

namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k]

/-- Original sections which are Nisnevich-locally zero give the zero transfer
sheaf under the existing transfer-preserving sheafification functor. -/
theorem isZero_nisnevichSheafify_of_locally_zero (P : PresheafWithTransfers.{u + 1} k)
    (hP : ∀ (X : SmoothSite (Spec (.of k)))
      (s : ((toPresheaf k).obj P).obj (op X)),
      Presheaf.equalizerSieve s 0 ∈ SmoothSite.nisnevichTopology (Spec (.of k)) X) :
    IsZero ((nisnevichSheafify k).obj P) := by
  let J := SmoothSite.nisnevichTopology (Spec (.of k))
  let Q := (toPresheaf k).obj P
  have ho : IsZero ((presheafToSheaf J AddCommGrpCat.{u + 1}).obj Q) :=
    Presheaf.isZero_sheafify_of_locally_zero J Q hP
  have hu : IsZero ((SheafWithTransfers.toSheaf k).obj ((nisnevichSheafify k).obj P)) :=
    ho.of_iso ((nisnevichSheafificationUnderlyingIso k).app P).symm
  apply (IsZero.iff_id_eq_zero _).mpr
  apply (SheafWithTransfers.toSheaf k).zero_of_map_zero
  exact ((SheafWithTransfers.toSheaf k).map_id _).trans ((IsZero.iff_id_eq_zero _).mp hu)

end Motivic.PresheafWithTransfers
