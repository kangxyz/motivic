/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.LocalVanishing.GenericBase.CylinderZero
import all Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Affine.LineOpenMaps
import all Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Cartier.CylinderOpenImage
import all Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.WholeBase.CylinderTransport
import all Motivic.Cohomology.A1.LocalVanishing.GenericBase.CylinderZero
import Lean
public import Batteries.Tactic.Lint

/-! # Original affine-cylinder generic-base vanishing without presentation inputs -/

@[expose] public noncomputable section
open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory AlgebraicGeometry Opposite
universe w u
namespace MotivicTest.RelativeGenericBaseCylinderZero
open _root_.AlgebraicGeometry.Scheme.SmoothSite
open _root_.AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
open Motivic
open _root_.AlgebraicGeometry.Scheme.SmoothSite
open _root_.CategoryTheory.Sheaf.LargeCohomology
open _root_.Motivic.SheafCohomology
variable {k : Type u} [Field k]
  [HasExt.{w} (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The conclusion uses the original source, generic point and whole-cylinder map. -/
theorem original_positive_cylinder_class_zero
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant) (n : ℕ)
    (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left]
    (x : H.{w, u + 1, u, u + 1} (nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) (n + 1) (a1Cylinder (.of k) X)) :
    ∃ V : X.left.Opens, IsAffineOpen V ∧ genericPoint X.left ∈ V ∧
      (presheaf.{w, u + 1, u, u + 1} (nisnevichTopology (Spec (.of k)))
        ((SheafWithTransfers.toSheaf k).obj F) (n + 1)).map
          (a1Map (.of k) (openInclusion X V)).op x = 0 :=
  exists_generic_base_cylinder_positive_zero F hF n X x

open Lean in
run_cmd do
  for name in #[``original_positive_cylinder_class_zero,
      ``exists_generic_base_cylinder_positive_zero,
      ``exists_affine_generic_open_cylinder_zero_of_openImmersion,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.cylinder_zero_on_open_image,
      ``cylinder_restriction_zero_of_lineBaseOpen,
      ``lineBaseOpenCylinder_two_maps,
      ``lineBaseOpenCylinderIso_comp,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates.lineBaseOpen_isPullback,
      ``lineCylinderIso_naturality,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates.affineLineIso_projection,
      ``exists_relative_generic_base_positive_zero] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original generic-base whole-cylinder restriction: standard axioms only."

open Lean Batteries.Tactic.Lint in
run_cmd do
  let declarations := #[``original_positive_cylinder_class_zero,
    ``exists_generic_base_cylinder_positive_zero,
    ``exists_affine_generic_open_cylinder_zero_of_openImmersion,
    ``_root_.AlgebraicGeometry.Scheme.SmoothSite.cylinder_zero_on_open_image,
    ``cylinder_restriction_zero_of_lineBaseOpen,
    ``lineBaseOpenCylinder_two_maps,
    ``_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates.lineBaseOpenCylinderIso,
    ``lineBaseOpenCylinderIso_comp,
    ``_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates.lineBaseOpen_isPullback,
    ``lineCylinderIso_naturality,
    ``_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates.affineLineIso_projection]
  let linters ← Lean.Elab.Command.liftCoreM (getChecks true none none)
  unless !linters.isEmpty do
    throwError "No declaration linters were selected."
  let results ← Lean.Elab.Command.liftCoreM <|
    Lean.withExporting (isExporting := false) (lintCore declarations linters)
  for (linter, findings) in results do
    for (name, message) in findings.toArray do
      throwError "{linter.name}: {name}: {message}"
  logInfo "Original generic-base whole-cylinder restriction: declaration linters passed."

end MotivicTest.RelativeGenericBaseCylinderZero
