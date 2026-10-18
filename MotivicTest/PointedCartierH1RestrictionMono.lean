/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.PointedCartierH1RestrictionMono
import all Motivic.AlgebraicGeometry.SmoothSiteProductPermutation
import all Motivic.AlgebraicGeometry.Sites.FiniteEtaleSmoothNeighborhood
import all Motivic.Cohomology.A1.ContractionBoundaryProjectionGeometry
import all Motivic.Cohomology.A1.ContractionBoundaryProjection
import all Motivic.Cohomology.A1.ContractionBoundaryProjectionCompatibility
import all Motivic.Cohomology.A1.ContractionBoundaryProjectionSupport
import all Motivic.Cohomology.A1.ContractionBoundaryProjectionExcisionGeometry
import all Motivic.Cohomology.A1.ContractionBoundaryProjectionExcision
import all Motivic.AlgebraicGeometry.SmoothSiteContractionDensity
import all Motivic.Cohomology.A1.PointedCylinderLocalEffacement
import all Motivic.Cohomology.A1.PointedCylinderH1ChartVanishing
import all Motivic.Cohomology.A1.PointedEtaleCylinderRestriction
import all Motivic.Cohomology.A1.PointedCartierH1RestrictionMono
public import Lean.Util.CollectAxioms
public import Batteries.Tactic.Lint

/-! # The actual degree-one Cartier puncture restriction, with canonical Epi retained -/

public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open Scheme.Modules Scheme.Modules.Invertible

universe u

namespace MotivicTest.PointedCartierH1RestrictionMono

/-- The consumer is the literal original H1 puncture map at an arbitrary full
field-valued mark. Its only unproved mathematical input is canonical boundary
Epi for the original coefficient, not a cohomological restriction-Mono family. -/
theorem original_H1_cartier_puncture_injective
    (k : Type u) [Field k] [Infinite k]
    [HasExt.{u + 1}
      (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
    (Y : SmoothSite (Spec (.of k))) (F : SheafWithTransfers.{u + 1} k)
    (hF : F.obj.IsA1Invariant)
    (hE : ∀ X : SmoothSite (Spec (.of k)),
      Epi (FiniteEtaleSite.contractionToBoundary X F hF))
    {Z : Scheme.{u}} (i : Z ⟶ Y.left) [IsClosedImmersion i] [Smooth (i ≫ Y.hom)]
    (hI : IsLocallyRankOne Y.left (Scheme.Hom.idealModule i))
    {U : SmoothSite (Spec (.of k))} (j : U ⟶ Y) [IsOpenImmersion j.left]
    (hcomp : Set.range i = (Set.range j.left)ᶜ)
    (K : Type u) [Field K] (b : Spec (.of K) ⟶ Y.left) (s : Spec (.of K))
    (hb : b s ∈ Set.range i) :
    Function.Injective (colim.map (FiniteEtaleSite.pointedCylinderRestriction (.of k) j
      (FiniteEtaleSite.relativeFieldPoint b K (𝟙 _))
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k)))
          ((SheafWithTransfers.toSheaf k).obj F) 1))) := by
  apply (AddCommGrpCat.mono_iff_injective _).mp
  exact FiniteEtaleSite.pointedCylinderRestriction_H1_mono_of_cartier_of_boundary_epi
    Y F hF hE i hI j hcomp K b s hb

open Lean in
run_cmd do
  for name in #[``original_H1_cartier_puncture_injective,
      ``FiniteEtaleSite.contractionAmbientProjectionMap_π,
      ``FiniteEtaleSite.contractionBoundaryProjection_unit,
      ``FiniteEtaleSite.contractionToBoundary_projection,
      ``FiniteEtaleSite.contractionChartAmbientProjectionMap_eq_a1,
      ``FiniteEtaleSite.a1AmbientProjectionMap_π,
      ``FiniteEtaleSite.a1PunctureProjectionBaseChangeIso_restriction,
      ``FiniteEtaleSite.fieldPoint_etale_restriction_comparison] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual full-marked Cartier H1 restriction: standard foundations only."

open Lean Batteries.Tactic.Lint in
run_cmd do
  let env ← getEnv
  let sourceModules := #[`Motivic.AlgebraicGeometry.SmoothSiteProductPermutation,
    `Motivic.AlgebraicGeometry.Sites.FiniteEtaleSmoothNeighborhood,
    `Motivic.Cohomology.A1.ContractionBoundaryProjectionGeometry,
    `Motivic.Cohomology.A1.ContractionBoundaryProjection,
    `Motivic.Cohomology.A1.ContractionBoundaryProjectionCompatibility,
    `Motivic.Cohomology.A1.ContractionBoundaryProjectionSupport,
    `Motivic.Cohomology.A1.ContractionBoundaryProjectionExcisionGeometry,
    `Motivic.Cohomology.A1.ContractionBoundaryProjectionExcision,
    `Motivic.AlgebraicGeometry.SmoothSiteContractionDensity,
    `Motivic.Cohomology.A1.PointedCylinderLocalEffacement,
    `Motivic.Cohomology.A1.PointedCylinderH1ChartVanishing,
    `Motivic.Cohomology.A1.PointedEtaleCylinderRestriction,
    `Motivic.Cohomology.A1.PointedCartierH1RestrictionMono]
  let modules := env.header.moduleNames.map (sourceModules.contains ·)
  let declarations := env.constants.map₁.fold
    (init := ← Lean.Elab.Command.liftCoreM getDeclsInCurrModule) fun declarations name _ =>
      if modules[env.const2ModIdx[name]?.get!]! then declarations.push name else declarations
  unless declarations.size ≥ 40 do
    throwError "The actual product, chart, and original-point declarations are missing from lint."
  let linters ← Lean.Elab.Command.liftCoreM (getChecks true none none)
  unless !linters.isEmpty do
    throwError "No declaration linters were selected."
  let results ← Lean.Elab.Command.liftCoreM <|
    Lean.withExporting (isExporting := false) (lintCore declarations linters)
  let mut failed := false
  for (linter, findings) in results do
    for (name, message) in findings.toArray do
      logError m!"{linter.name}: {name}: {message}"
      failed := true
  if failed then
    throwError "The exact-origin declaration lint found errors."
  logInfo m!"Actual Cartier H1 puncture restriction: {declarations.size} declarations passed lint."

end MotivicTest.PointedCartierH1RestrictionMono
