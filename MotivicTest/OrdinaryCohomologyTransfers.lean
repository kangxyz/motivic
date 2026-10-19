/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Cohomology.Basic
public import Lean.Util.CollectAxioms

/-! Signed transfers on original ordinary H, with literal graph and coefficient maps. -/
@[expose] public noncomputable section
open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry Opposite
universe w w' u
namespace MotivicTest.OrdinaryCohomologyTransfers
open Motivic Motivic.SheafWithTransfers
variable (k : Type u) [Field k]
  [HasExt.{w} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{w'} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  (F : SheafWithTransfers.{u + 1} k) (n : ℕ)

/-- The transferred group is literally the original ordinary cohomology group. -/
example (X : Cor k) :
    (ordinaryCohomologyTransfers.{w, w', u} k F n).sections X =
      _root_.CategoryTheory.Sheaf.LargeCohomology.H.{w', u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) ((toSheaf k).obj F) n X.toSmoothSite := rfl

/-- Every actual graph acts by the old ordinary restriction, not a new map. -/
theorem actual_graph_restriction {X Y : SmoothSite (Spec (.of k))} (f : X ⟶ Y)
    (e : _root_.CategoryTheory.Sheaf.LargeCohomology.H.{w', u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k))) ((toSheaf k).obj F) n Y) :
    (ordinaryCohomologyTransfers.{w, w', u} k F n).transfer ((Cor.graphFunctor k).map f) e =
      (_root_.CategoryTheory.Sheaf.LargeCohomology.presheaf.{w', u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) ((toSheaf k).obj F) n).map f.op e :=
  ordinaryCohomologyTransfers_graph k F n f e

/-- Genuine signed correspondence composition acts contravariantly. -/
theorem actual_signed_composition {X Y Z : Cor k} (a : X ⟶ Y) (b : Y ⟶ Z) :
    (ordinaryCohomologyTransfers.{w, w', u} k F n).transfer (a ≫ b) =
      (ordinaryCohomologyTransfers.{w, w', u} k F n).transfer b ≫
        (ordinaryCohomologyTransfers.{w, w', u} k F n).transfer a :=
  PresheafWithTransfers.transfer_comp _ a b

open Lean in
run_cmd do
  for name in #[``actual_graph_restriction, ``actual_signed_composition,
      ``SheafWithTransfers.ordinaryCohomologyTransfers,
      ``SheafWithTransfers.ordinaryCohomologyTransfersGraphIso,
      ``SheafWithTransfers.ordinaryCohomologyTransfersMap,
      ``SheafCohomology.withTransfers,
      ``SheafCohomology.withTransfersGraphIso,
      ``SheafCohomology.withTransfers_graph,
      ``SheafCohomology.withTransfersMap] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original ordinary H with signed transfers: standard foundations only."

end MotivicTest.OrdinaryCohomologyTransfers

namespace MotivicTest.CanonicalOrdinaryCohomologyTransfers
open Motivic
variable (k : Type u) [Field k]
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- No transfer-category Ext or acyclicity assumption is required by the final endpoint. -/
example (F : SheafWithTransfers.{u + 1} k) (n : ℕ) (X : Cor k) :
    (SheafCohomology.withTransfers k F n).sections X =
      _root_.CategoryTheory.Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k)))
        ((SheafWithTransfers.toSheaf k).obj F) n X.toSmoothSite := rfl

end MotivicTest.CanonicalOrdinaryCohomologyTransfers
