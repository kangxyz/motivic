/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.PrincipalOrder
public import Motivic.AlgebraicGeometry.PresheavesWithTransfers.StaticBoundaryPencilAction
import all Motivic.Aglib.AlgebraicGeometry.RelativeCurve.BoundaryNeighborhoodComplement
import all Motivic.AlgebraicGeometry.Cycles.CodimensionOneDominance
import all Motivic.AlgebraicGeometry.Cycles.PrincipalOrderCycle
import all Motivic.AlgebraicGeometry.Correspondences.PrincipalOrder
import all Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.BoundaryFramedSectionTransport
import all Motivic.AlgebraicGeometry.PresheavesWithTransfers.StaticBoundaryPencilAction
public import Lean.Util.CollectAxioms
public import Batteries.Tactic.Lint
public import Mathlib.Tactic.Linter.TextBased

/-!
# Original principal correspondences and represented boundary-class actions

These consumers exercise the actual correspondence producer and the original
whole-divisor action theorem. The exact-origin audit includes all six new
production leaves, not the already accepted framed-class foundations. This
scope does not assert a principal A1 relation or the full standard-triple theorem.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
open Motivic
open scoped BigOperators

universe u v

namespace MotivicTest.StandardTripleGeometricConsumers

open Classical in
/-- The actual correspondence exists with its original native order and residue
weights, without a supplied admissible cycle or flatness of its supports. -/
theorem exists_original_principal_correspondence
    {k : Type u} [Field k] {X Y : SmoothSite (Spec (.of k))}
    [IsAffine X.left] {C V : Scheme.{u}} [IsIntegral C] [IsNoetherian C]
    [V.IsQuasiAffine] (q : C ⟶ X.left) [IsProper q]
    (j : V ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)]
    (U : C.Opens) [Nonempty U] (hU : (Set.range j)ᶜ ⊆ (U : Set C))
    (h : Γ(C, U)) (hh : IsUnit h) (g : V ⟶ Y.left)
    (hbase : j ≫ q ≫ X.hom = g ≫ Y.hom) :
    ∃ α : Cor.mk X ⟶ Cor.mk Y,
      ∀ W : FiniteCorrespondenceGenerator X.hom Y.hom,
        (show FiniteCorrespondence X.hom Y.hom from α) W =
          ∑ x : (principalOrderCycle U h hh).support,
            if PrincipalOrderCorrespondence.generator q j U hU h hh g hbase x = W then
              C.ord (C.germToFunctionField U h) x.val *
                ((PrincipalOrderCorrespondence.productMap q j U hU h hh g hbase x).residueDegree
                  (genericPoint (PrincipalOrderCorrespondence.supportScheme U h hh x)) : ℤ)
            else 0 := by
  exact ⟨PrincipalOrderCorrespondence.correspondence q j U hU h hh g hbase,
    PrincipalOrderCorrespondence.correspondence_coefficient q j U hU h hh g hbase⟩

/-- Already represented equal boundary-framed classes act identically through
their original whole zero schemes; the polynomial homotopy is constructed. -/
theorem original_divisor_actions_of_represented_class_equality
    {k : Type u} [Field k] (X Y : SmoothSite (Spec (.of k))) [IsAffine X.left]
    {C B U : Scheme.{u}} (i : B ⟶ C) (q : C ⟶ X.left) [IsProper q]
    (j : U ⟶ C) [IsOpenImmersion j] [U.IsQuasiAffine]
    [SmoothOfRelativeDimension 1 (j ≫ q)] (L M : LineBundle C)
    (hcover : ∀ x : C, x ∈ Set.range j ∨ x ∈ Set.range i)
    (g : U ⟶ Y.left) (hbase : (j ≫ q) ≫ X.hom = g ≫ Y.hom)
    (P : PresheafWithTransfers.{v} k) (hP : P.IsA1Invariant)
    (s : SheafOfModules.unit C.ringCatSheaf ⟶ L.val)
    (t : SheafOfModules.unit C.ringCatSheaf ⟶ M.val)
    [IsIso (pullbackSectionMap i s)] [IsIso (pullbackSectionMap i t)]
    (he : BoundaryFramedLineBundle.classOf (BoundaryFramedLineBundle.ofSection i L s) =
      BoundaryFramedLineBundle.classOf (BoundaryFramedLineBundle.ofSection i M t)) :
    P.transfer (Cor.boundarySection X Y i q j L hcover g hbase s) =
      P.transfer (Cor.boundarySection X Y i q j M hcover g hbase t) :=
  PresheafWithTransfers.transfer_boundarySection_eq_of_class_eq
    X Y i q j L hcover g hbase P hP M s t he

open Lean Batteries.Tactic.Lint in
run_cmd do
  let env ← getEnv
  let sourceModules := #[
    `Motivic.Aglib.AlgebraicGeometry.RelativeCurve.BoundaryNeighborhoodComplement,
    `Motivic.AlgebraicGeometry.Cycles.CodimensionOneDominance,
    `Motivic.AlgebraicGeometry.Cycles.PrincipalOrderCycle,
    `Motivic.AlgebraicGeometry.Correspondences.PrincipalOrder,
    `Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.BoundaryFramedSectionTransport,
    `Motivic.AlgebraicGeometry.PresheavesWithTransfers.StaticBoundaryPencilAction]
  let modules := env.header.moduleNames.map (sourceModules.contains ·)
  let declarations := env.constants.map₁.fold
    (init := ← Lean.Elab.Command.liftCoreM getDeclsInCurrModule) fun declarations name _ =>
      if modules[env.const2ModIdx[name]?.get!]! then declarations.push name else declarations
  unless declarations.size ≥ 35 do
    throwError "Exact-origin geometry and original-action declarations are missing."
  for name in declarations do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  let linters ← Lean.Elab.Command.liftCoreM (getChecks true none none)
  unless !linters.isEmpty do
    throwError "No declaration linters selected."
  let results ← Lean.Elab.Command.liftCoreM <|
    Lean.withExporting (isExporting := false) (lintCore declarations linters)
  for (linter, findings) in results do
    for (name, message) in findings.toArray do
      throwError "{linter.name}: {name}: {message}"
  logInfo m!"All {declarations.size} exact-origin declarations: lint and standard axioms passed."

open Lean Mathlib.Linter.TextBased in
run_cmd do
  let options : Lean.Linter.LinterOptions := {
    toOptions := ← getOptions
    linterSets := (Lean.Linter.linterSetsExt.getState (← getEnv)).merged }
  let modules := #[
    `Motivic.Aglib.AlgebraicGeometry.RelativeCurve.BoundaryNeighborhoodComplement,
    `Motivic.AlgebraicGeometry.Cycles.CodimensionOneDominance,
    `Motivic.AlgebraicGeometry.Cycles.PrincipalOrderCycle,
    `Motivic.AlgebraicGeometry.Correspondences.PrincipalOrder,
    `Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.BoundaryFramedSectionTransport,
    `Motivic.AlgebraicGeometry.PresheavesWithTransfers.StaticBoundaryPencilAction,
    `MotivicTest.StandardTripleGeometricConsumers]
  let errors ← lintModules options #[] modules .humanReadable false
  let casingErrors ← modulesNotUpperCamelCase options modules
  let filenameErrors ← modulesOSForbidden options modules
  unless errors == 0 && casingErrors == 0 && filenameErrors == 0 do
    throwError "Exact-file source text/style checks failed."
  logInfo "Pinned text/style checks passed for all seven selected modules."

end MotivicTest.StandardTripleGeometricConsumers
