/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.Sheafification.CylinderCriterion
public import Motivic.Cohomology.A1.StrictInvariance.PerfectField
public import Motivic.Cohomology.A1.Sheafification.StrictInvariance

import all Motivic.Transfers.Presheaf.Sheafification.Image
import all Motivic.Cohomology.A1.Sheafification.DenseDetection
import all Motivic.Cohomology.A1.Sheafification.CylinderCriterion
import all Motivic.Cohomology.A1.Sheafification.StrictInvariance
import Mathlib.Tactic.Linter
import Mathlib.Tactic.Linter.TextBased


/-!
# Original HI-presheaf sheafification reduction consumers

The image and dense-detection assertions are unconditional for an original HI
presheaf. The HI and strict-cohomological conclusions explicitly retain the
whole-cylinder lifting hypothesis. This test does not claim the full
HI-presheaf sheafification theorem.
-/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Motivic
open Motivic.PresheafWithTransfers

universe u v

namespace MotivicTest.HIPresheafSheafificationReduction

variable {k : Type u} [Field k]

/-- Epi descent needs HI only on the original source, at independent coefficient size. -/
theorem quotient_isA1Invariant {P Q : PresheafWithTransfers.{v} k} (η : P ⟶ Q)
    [∀ X : Cor k, Epi (η.hom.app (op X))] (hP : P.IsA1Invariant) :
    Q.IsA1Invariant :=
  isA1Invariant_of_epi_app η hP

/-- The image factorization retains the original transfer-natural unit. -/
theorem original_unit_factorization (P : PresheafWithTransfers.{u + 1} k) :
    toNisnevichImage P ≫ nisnevichImageι P = toNisnevichSheafify k P :=
  toNisnevichImage_ι P

/-- The actual image of the unit, not a supplied replacement coefficient, is HI. -/
theorem actual_image_isA1Invariant (P : PresheafWithTransfers.{u + 1} k)
    (hP : P.IsA1Invariant) : (nisnevichImage P).IsA1Invariant :=
  nisnevichImage_isA1Invariant P hP

/-- The original image is separated without an HI premise on its sheafification. -/
theorem actual_image_isSeparated (P : PresheafWithTransfers.{u + 1} k) :
    Presheaf.IsSeparated (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((toPresheaf k).obj (nisnevichImage P)) :=
  nisnevichImage_isSeparated P

/-- Sheafifying the actual image identifies its unit with the unchanged inclusion. -/
theorem actual_image_comparison_unit (P : PresheafWithTransfers.{u + 1} k) :
    toSheafify (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((toPresheaf k).obj (nisnevichImage P)) ≫
      (nisnevichImageSheafificationIso P).hom.hom =
        (toPresheaf k).map (nisnevichImageι P) :=
  toSheafify_nisnevichImageSheafificationIso P

/-- The image inclusion locally generates the canonical sheafification. -/
theorem actual_image_local_generation (P : PresheafWithTransfers.{u + 1} k) :
    Presheaf.IsLocallySurjective (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((toPresheaf k).map (nisnevichImageι P)) := inferInstance

/-- The literal dense-open restriction of the canonical target is injective. -/
theorem original_dense_restriction_injective
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    {X A : SmoothSite (Spec (.of k))} (a : A ⟶ X) [IsOpenImmersion a.left]
    (ha : DenseRange a.left) :
    Function.Injective (((nisnevichSheafify k).obj P).obj.transfer
      ((Cor.graphFunctor k).map a)) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro s hs
  exact nisnevichSheafify_section_eq_zero_of_dense_open P hP a ha s hs

/-- The conditional input retains a whole cylinder over a nonempty base open. -/
theorem whole_cylinder_witness
    (P : PresheafWithTransfers.{u + 1} k) (hL : ModelWholeCylinderLifting P)
    (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left]
    (g : ((nisnevichSheafify k).obj P).obj.sections
      (Cor.mk (SmoothSite.a1Cylinder (.of k) X))) :
    ∃ (U : SmoothSite (Spec (.of k))) (j : U ⟶ X),
      IsOpenImmersion j.left ∧ Nonempty U.left ∧
      ∃ t : (nisnevichImage P).sections (Cor.mk (SmoothSite.a1Cylinder (.of k) U)),
        (nisnevichImageι P).hom.app (op (Cor.mk (SmoothSite.a1Cylinder (.of k) U))) t =
          ((nisnevichSheafify k).obj P).obj.transfer
            ((Cor.graphFunctor k).map (SmoothSite.a1Map (.of k) j)) g :=
  hL X g

/-- Actual sheafification HI is conditional only on the displayed lifting input. -/
theorem sheafification_isA1Invariant_of_lifting
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (hL : ModelWholeCylinderLifting P) :
    ((nisnevichSheafify k).obj P).obj.IsA1Invariant :=
  nisnevichSheafify_isA1Invariant_of_modelWholeCylinderLifting P hP hL

section Strict

variable [PerfectField k]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Conditional strict invariance preserves every original ordinary projection. -/
theorem original_cohomology_projection_isIso_of_lifting
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (hL : ModelWholeCylinderLifting P) (n : ℕ)
    (X : SmoothSite (Spec (.of k))) :
    IsIso ((_root_.CategoryTheory.Sheaf.LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k)))
        ((SheafWithTransfers.toSheaf k).obj ((nisnevichSheafify k).obj P)) n).map
          (SmoothSite.a1Projection (.of k) X).op) :=
  nisnevichSheafify_isStrictA1Invariant_of_modelWholeCylinderLifting P hP hL n X

/-- Degree zero is the same original ordinary cohomological projection. -/
theorem original_degreeZero_projection_isIso_of_lifting
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (hL : ModelWholeCylinderLifting P) (X : SmoothSite (Spec (.of k))) :
    IsIso ((_root_.CategoryTheory.Sheaf.LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k)))
        ((SheafWithTransfers.toSheaf k).obj ((nisnevichSheafify k).obj P)) 0).map
          (SmoothSite.a1Projection (.of k) X).op) :=
  nisnevichSheafify_isStrictA1Invariant_of_modelWholeCylinderLifting P hP hL 0 X

end Strict

open Lean Batteries.Tactic.Lint in
run_cmd do
  let env ← getEnv
  let sourceModules := #[
    `Motivic.Transfers.Presheaf.Sheafification.Image,
    `Motivic.Cohomology.A1.Sheafification.DenseDetection,
    `Motivic.Cohomology.A1.Sheafification.CylinderCriterion,
    `Motivic.Cohomology.A1.Sheafification.StrictInvariance]
  for sourceModule in sourceModules do
    unless env.header.moduleNames.contains sourceModule do
      throwError "Required exact-origin module {sourceModule} is missing."
  let modules := env.header.moduleNames.map (sourceModules.contains ·)
  let declarations := env.constants.map₁.fold
    (init := ← Lean.Elab.Command.liftCoreM getDeclsInCurrModule) fun declarations name _ =>
      if modules[env.const2ModIdx[name]?.get!]! then declarations.push name else declarations
  unless declarations.size ≥ 20 do
    throwError "Exact-origin HI-presheaf reduction declarations are missing."
  for name in declarations do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  let linters ← Lean.Elab.Command.liftCoreM (getChecks true none none)
  unless !linters.isEmpty do
    throwError "No declaration linters selected."
  let results ← Lean.Elab.Command.liftCoreM <|
    Lean.withExporting (isExporting := false) (lintCore declarations linters)
  let mut failed := false
  for (linter, findings) in results do
    for (name, message) in findings.toArray do
      failed := true
      logError m!"{linter.name}: {name}: {message}"
  if failed then
    throwError "Exact-origin declaration lint failed; all findings are listed above."
  logInfo m!"All {declarations.size} exact-origin declarations: lint and standard axioms passed."

open Lean Mathlib.Linter.TextBased in
run_cmd do
  let options : Lean.Linter.LinterOptions := {
    toOptions := ← getOptions
    linterSets := (Lean.Linter.linterSetsExt.getState (← getEnv)).merged }
  let modules := #[
    `Motivic.Transfers.Presheaf.Sheafification.Image,
    `Motivic.Cohomology.A1.Sheafification.DenseDetection,
    `Motivic.Cohomology.A1.Sheafification.CylinderCriterion,
    `Motivic.Cohomology.A1.Sheafification.StrictInvariance,
    `MotivicTest.HIPresheafSheafificationReduction]
  let errors ← lintModules options #[] modules .humanReadable false
  let casingErrors ← modulesNotUpperCamelCase options modules
  let filenameErrors ← modulesOSForbidden options modules
  unless errors == 0 && casingErrors == 0 && filenameErrors == 0 do
    throwError "Exact-file source text/style checks failed."
  logInfo "Pinned text/style checks passed for the five selected modules."

end MotivicTest.HIPresheafSheafificationReduction
