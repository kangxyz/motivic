/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Cohomology.DegreeZero.Naturality
public import Lean.Util.CollectAxioms

/-! # Actual coefficient naturality of signed degree-zero transfers -/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory AlgebraicGeometry Motivic

universe u

namespace MotivicTest.Transfers.DegreeZeroNaturality

variable {k : Type u} [Field k]

local instance : HasExt.{u + 2}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}) :=
  HasExt.standard _

/-- Arbitrary coefficient morphisms commute with signed correspondence actions. -/
theorem actual_signed_coefficient_map {F G : SheafWithTransfers.{u + 1} k}
    (η : F ⟶ G) {X Y : Cor k} (α β : X ⟶ Y) :
    SheafWithTransfers.degreeZeroTransfer F ((-2 : ℤ) • (α - β)) ≫
        SheafWithTransfers.degreeZeroMap η X =
      SheafWithTransfers.degreeZeroMap η Y ≫
        SheafWithTransfers.degreeZeroTransfer G ((-2 : ℤ) • (α - β)) :=
  SheafWithTransfers.degreeZeroTransfer_naturality η _

open Lean in
run_cmd do
  for name in #[``Motivic.SheafWithTransfers.degreeZeroSectionsEquiv_map,
      ``Motivic.SheafWithTransfers.degreeZeroTransfer_naturality,
      ``actual_signed_coefficient_map] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Degree-zero transfer naturality uses only standard Lean logical foundations."

end MotivicTest.Transfers.DegreeZeroNaturality
