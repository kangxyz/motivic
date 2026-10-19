/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Cohomology.DegreeZero.Basic
public import Lean.Util.CollectAxioms

/-!
# Consumers of actual degree-zero cohomological transfers

These tests use the standard existing Ext construction and arbitrary fields.
They retain signed correspondence actions and verify agreement with each
actual graph restriction. No positive-degree transfer assumption is supplied.
-/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry Opposite Motivic

universe u

namespace MotivicTest.Transfers.DegreeZeroTransfers

variable {k : Type u} [Field k]

local instance : HasExt.{u + 2}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}) :=
  HasExt.standard _

/-- Signed differences act on the genuine cohomology groups through actual transfers. -/
theorem signed_transfer (F : SheafWithTransfers.{u + 1} k)
    {X Y : Cor k} (α β : X ⟶ Y) :
    SheafWithTransfers.degreeZeroTransfer F ((-3 : ℤ) • (α - β)) =
      (-3 : ℤ) • (SheafWithTransfers.degreeZeroTransfer F α -
        SheafWithTransfers.degreeZeroTransfer F β) := by
  change PresheafWithTransfers.transfer
      (SheafWithTransfers.degreeZeroPresheafWithTransfers F) ((-3 : ℤ) • (α - β)) = _
  rw [PresheafWithTransfers.transfer_zsmul, PresheafWithTransfers.transfer_sub]
  rfl

/-- The transfer along every graph is exactly the actual ordinary cohomology map. -/
theorem actual_graph_restriction (F : SheafWithTransfers.{u + 1} k)
    {X Y : SmoothSite (Spec (.of k))} (f : X ⟶ Y) :
    SheafWithTransfers.degreeZeroTransfer F ((Cor.graphFunctor k).map f) =
      (_root_.CategoryTheory.Sheaf.LargeCohomology.presheaf.{u + 2, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k)))
        ((SheafWithTransfers.toSheaf k).obj F) 0).map f.op :=
  SheafWithTransfers.degreeZeroTransfer_graph F f

/-- The degree-zero comparison intertwines actual restriction with ordinary section restriction. -/
theorem actual_section_restriction (F : SheafWithTransfers.{u + 1} k)
    {X Y : SmoothSite (Spec (.of k))} (f : X ⟶ Y)
    (x : _root_.CategoryTheory.Sheaf.LargeCohomology.H.{u + 2, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) 0 Y) :
    SheafWithTransfers.degreeZeroSectionsEquiv F (Cor.mk X)
        ((_root_.CategoryTheory.Sheaf.LargeCohomology.presheaf.{u + 2, u + 1}
          (SmoothSite.nisnevichTopology (Spec (.of k)))
          ((SheafWithTransfers.toSheaf k).obj F) 0).map f.op x) =
      PresheafWithTransfers.transfer F.obj ((Cor.graphFunctor k).map f)
        (SheafWithTransfers.degreeZeroSectionsEquiv F (Cor.mk Y) x) :=
  _root_.CategoryTheory.Sheaf.LargeCohomology.zeroSections_restriction.{u + 2, u + 1} _ _ f x

open Lean in
run_cmd do
  for name in #[``_root_.CategoryTheory.Sheaf.Hypercohomology.sectionsAddEquiv_naturality_left,
      ``_root_.CategoryTheory.Sheaf.LargeCohomology.zeroSections,
      ``_root_.CategoryTheory.Sheaf.LargeCohomology.zeroSections_restriction,
      ``_root_.CategoryTheory.Sheaf.LargeCohomology.zeroSections_naturality,
      ``Motivic.SheafWithTransfers.degreeZeroPresheafWithTransfers,
      ``Motivic.SheafWithTransfers.degreeZeroUnderlyingIso,
      ``signed_transfer, ``actual_graph_restriction, ``actual_section_restriction] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual degree-zero cohomological transfers use only standard Lean logical foundations."

end MotivicTest.Transfers.DegreeZeroTransfers
