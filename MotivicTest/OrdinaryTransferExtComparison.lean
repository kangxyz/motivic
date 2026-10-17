/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Motivic.Transfers.OrdinaryTransferExtComparison
import Lean

/-! # Actual transfer-to-ordinary Ext comparison, independent universes -/
noncomputable section

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry Opposite
open Motivic Motivic.SheafWithTransfers
universe w w' u
namespace MotivicTest.OrdinaryTransferExtComparison
variable (k : Type u) [Field k]
  [HasExt.{w} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{w'} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- This tests the original cohomology group, not a replacement provider. -/
example (X : SmoothSite (Spec (.of k))) (F : SheafWithTransfers.{u + 1} k) (n : ℕ) :
    Ext.{w} ((transferRepresentable k).obj (Cor.mk X)) F n ≃+
      SheafCohomology.H.{w', u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) ((toSheaf k).obj F) n X :=
  transferExtEquiv k X F n

/-- Actual graph restriction is unchanged in every degree. -/
example {X Y : SmoothSite (Spec (.of k))} (f : X ⟶ Y)
    (F : SheafWithTransfers.{u + 1} k) (n : ℕ)
    (e : Ext.{w} ((transferRepresentable k).obj (Cor.mk Y)) F n) :
    transferExtEquiv k X F n
      ((Ext.mk₀ ((transferRepresentable k).map ((Cor.graphFunctor k).map f))).comp e
        (zero_add n)) =
      (SheafCohomology.presheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
        ((toSheaf k).obj F) n).map f.op (transferExtEquiv k Y F n e) :=
  transferExtEquiv_naturality_graph k f F n e

open Lean in
run_cmd do
  for name in #[``transferExtComparison_bijective, ``transferExtEquiv,
      ``transferExtEquiv_naturality_coeff, ``transferExtEquiv_naturality_graph] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual all-degree Ext comparison and both naturalities: standard foundations only."

end MotivicTest.OrdinaryTransferExtComparison
