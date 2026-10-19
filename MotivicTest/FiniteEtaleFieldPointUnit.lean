/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Field.Point.Unit
public import Lean.Util.CollectAxioms

/-! The genuine inverse-image comparison preserves its actual adjunction-unit representatives. -/
@[expose] public noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
universe u
namespace MotivicTest.FiniteEtaleFieldPointUnit
open _root_.AlgebraicGeometry.Scheme (EtaleSeparatedFiniteType)
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable {S T : Scheme.{u}} (b : S ⟶ T) (K : Type u) [Field K]
  (q : Spec (.of K) ⟶ S) [Etale q] [IsSeparated q] [QuasiCompact q]

/-- The map is the original unit followed by the actual field-valued restriction. -/
theorem actual_unit_representative
    (G : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1})
    (V : EtaleSeparatedFiniteType T) (a : fieldObject K q ⟶ (baseChange b).obj V) :
    (relativeFieldPoint b K q).toPresheafFiber V
        (shrinkYonedaObjObjEquiv.{u + 1}.symm a) G.obj ≫
      (relativeFieldPointInverseImageIso b K q).hom.app G =
    ((imageAdjunction b).unit.app G).hom.app (op V) ≫
      ((inverseImage b).obj G).obj.map a.op :=
  relativeFieldPointInverseImageIso_ι b K q G V a

open Lean in
run_cmd do
  for name in #[``actual_unit_representative,
      ``_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.pointAdjunctionUnit_π,
      ``relativeFieldPoint_comapIso_ι,
          ``_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.fieldPointPresheafFiberIso_ι,
      ``relativeFieldPointInverseImageIso_ι, ``fieldNeighborhoodInverseImageIso_ι] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual inverse-image unit representative formula: standard foundations only."

end MotivicTest.FiniteEtaleFieldPointUnit
