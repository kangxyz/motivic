/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Motivic.Transfers.Cohomology.Ext.OrdinarySource
import Lean

/-! # Direct audit of the actual section source and its naturality -/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory AlgebraicGeometry Motivic Motivic.SheafWithTransfers
universe u
namespace MotivicTest.OrdinaryTransferExtSource
variable (k : Type u) [Field k]

example : (transferRepresentable k).Additive := inferInstance

example (X : SmoothSite (Spec (.of k))) (F : SheafWithTransfers.{u + 1} k) :
    Function.Bijective (ordinaryTransferHomEquiv k X F) :=
  (ordinaryTransferHomEquiv k X F).bijective

open Lean in
run_cmd do
  for name in #[``transferRepresentable_additive, ``transferSectionsEquiv_naturality_left,
      ``ordinaryTransferHomEquiv_apply, ``ordinaryToTransferSource_naturality] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual ordinary-to-transfer source and naturality: standard foundations only."

end MotivicTest.OrdinaryTransferExtSource
