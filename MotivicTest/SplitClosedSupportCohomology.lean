/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleSplitClosedCohomology
import all Motivic.Aglib.AlgebraicGeometry.ClosedFiberEtaleEqualization
import all Motivic.AlgebraicGeometry.Sites.FiniteEtaleSplitClosedNeighborhood
import all Motivic.AlgebraicGeometry.Sites.FiniteEtaleSplitClosedPointFiber
import all Motivic.AlgebraicGeometry.Sites.FiniteEtaleSplitClosedComap
import all Motivic.AlgebraicGeometry.Sites.FiniteEtaleSplitClosedSupportUnit
import all Motivic.AlgebraicGeometry.Sites.FiniteEtaleSplitClosedImageExact
import all Motivic.AlgebraicGeometry.Sites.FiniteEtaleSplitClosedCohomology
import all Motivic.AlgebraicGeometry.Sites.FiniteEtaleDirectImageOpenSupport
import all Motivic.AlgebraicGeometry.Sites.FiniteEtalePointInverseImageComposition
public import Lean.Util.CollectAxioms
public import Batteries.Tactic.Lint

/-! Original sections and ordinary Ext on an actual supported split-closed chart. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace MotivicTest.SplitClosedSupportCohomology
open Motivic Motivic.FiniteEtaleSite
variable {Z U Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i] [IsNoetherian Y]
  (p : Y ⟶ Z) (hip : i ≫ p = 𝟙 Z)
  (j : U ⟶ Y) [IsOpenImmersion j] [QuasiCompact j]
  (hcomp : Set.range i = (Set.range j)ᶜ)
  (G : Sheaf (nisnevichTopology Y) AddCommGrpCat.{u + 1})
  (hG : IsZero ((inverseImage j).obj G)) (V : FiniteEtaleSite Y)

include p hip j hcomp hG

/-- Degree-one consumers may lift by the actual unit on sections, without
assuming a new retraction after the later local quotient lift. -/
theorem actual_unit_sections_bijective :
    Function.Bijective (((imageAdjunction i).unit.app G).hom.app (op V)) := by
  let := splitClosed_support_unit_isIso i p hip j hcomp G hG
  exact ConcreteCategory.bijective_of_isIso _

variable [HasExt.{u + 1} (Sheaf (nisnevichTopology Y) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (nisnevichTopology Z) AddCommGrpCat.{u + 1})]

/-- The comparison is bijective for the original inverse-image Ext map, not
merely for an unrelated choice of isomorphic groups. -/
theorem original_inverseImage_bijective (n : ℕ) :
    Function.Bijective (fun x : SheafCohomology.H.{u + 1, u + 1, u, u + 1}
      (nisnevichTopology Y) G n V =>
      (Abelian.Ext.mk₀ (inverseImageSourceIso i V).inv).comp
        (x.mapExactFunctor (inverseImage i)) (zero_add n)) := by
  have h := splitClosedSupportCohomology_bijective i p hip j hcomp V G hG n
  simp only [ordinarySupportComparison_eq_inverseImage] at h
  exact h

open Lean in
run_cmd do
  for name in #[``actual_unit_sections_bijective, ``original_inverseImage_bijective,
      ``Motivic.FiniteEtaleSite.splitClosed_support_unit_isIso,
      ``Motivic.FiniteEtaleSite.splitClosedComap_unit_compare,
      ``Motivic.FiniteEtaleSite.splitClosedDirectImage_preservesFiniteColimits,
      ``Motivic.FiniteEtaleSite.splitClosedOrdinaryEdgeMap_bijective,
      ``Motivic.FiniteEtaleSite.etaleRestriction_directImage_isZero_of_disjoint,
      ``Motivic.FiniteEtaleSite.inverseImage_directImage_isZero_of_disjoint,
      ``Motivic.FiniteEtaleSite.fieldPoint_directImage_isZero_of_mem_disjoint_open,
      ``Motivic.FiniteEtaleSite.fieldPoint_directImage_isZero_of_not_mem_range] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original supported sections, unit and ordinary Ext: standard axioms only."

open Lean Batteries.Tactic.Lint in
run_cmd do
  let env ← getEnv
  let sourceModules := #[
    `Motivic.Aglib.AlgebraicGeometry.ClosedFiberEtaleEqualization,
    `Motivic.AlgebraicGeometry.Sites.FiniteEtaleSplitClosedNeighborhood,
    `Motivic.AlgebraicGeometry.Sites.FiniteEtaleSplitClosedPointFiber,
    `Motivic.AlgebraicGeometry.Sites.FiniteEtaleSplitClosedComap,
    `Motivic.AlgebraicGeometry.Sites.FiniteEtaleSplitClosedSupportUnit,
    `Motivic.AlgebraicGeometry.Sites.FiniteEtaleSplitClosedImageExact,
    `Motivic.AlgebraicGeometry.Sites.FiniteEtaleSplitClosedCohomology,
    `Motivic.AlgebraicGeometry.Sites.FiniteEtaleDirectImageOpenSupport,
    `Motivic.AlgebraicGeometry.Sites.FiniteEtalePointInverseImageComposition]
  let modules := env.header.moduleNames.map (sourceModules.contains ·)
  let declarations := env.constants.map₁.fold
    (init := ← Lean.Elab.Command.liftCoreM getDeclsInCurrModule) fun declarations name _ =>
      if modules[env.const2ModIdx[name]?.get!]! then declarations.push name else declarations
  unless declarations.size ≥ 40 do
    throwError "Split-support declarations are missing from the exact-scope audit."
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
  logInfo "All {declarations.size} split-support declarations: lint and standard axioms passed."

end MotivicTest.SplitClosedSupportCohomology
