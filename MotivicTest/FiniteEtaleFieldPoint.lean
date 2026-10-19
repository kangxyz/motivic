/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Field.Point.InverseImage
public import Lean.Util.CollectAxioms

/-! Field evaluation and its genuine inverse-image comparison on the original small site. -/
@[expose] public noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
universe u
namespace MotivicTest.FiniteEtaleFieldPoint
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable {S T : Scheme.{u}} (b : S ⟶ T) (K : Type u) [Field K]
  (q : Spec (.of K) ⟶ S) [Etale q] [IsSeparated q] [QuasiCompact q]

/-- The target is evaluation of the existing inverse image of the original ordinary sheaf. -/
def actual_inverse_image_evaluation
    (F : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}) :
    (relativeFieldPoint b K q).sheafFiber.obj F ≅
      ((inverseImage b).obj F).obj.obj (op (fieldObject K q)) :=
  (relativeFieldPointInverseImageIso b K q).app F

open Lean in
run_cmd do
  for name in #[``actual_inverse_image_evaluation,
      ``_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.fieldObject_cover_lifting,
      ``_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.fieldPoint,
          ``_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.fieldPointPresheafFiberIso,
          ``_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.fieldPointSheafFiberIso,
      ``_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.relativeFieldPoint,
          ``relativeFieldPointInverseImageIso] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual small-site field point and inverse image: standard foundations only."

end MotivicTest.FiniteEtaleFieldPoint
