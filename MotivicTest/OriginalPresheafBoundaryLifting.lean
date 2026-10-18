/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.PresheafContractionBoundaryEpi
public import Motivic.Cohomology.A1.ContractionBoundarySheafComparison
public import Motivic.Cohomology.A1.ContractionBoundaryMono
import all Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.NeighborhoodPunctureIdentification
import all Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.NeighborhoodPunctureBaseChange
import all Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.NeighborhoodOriginalAmbientMaps
import all Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.PolynomialZeroOriginalEtalePresentation
import all Motivic.AlgebraicGeometry.Sites.FiniteEtaleJacobsonOpenCover
import all Motivic.AlgebraicGeometry.Sites.FiniteEtaleSmoothNeighborhood
import all Motivic.AlgebraicGeometry.SmoothSiteAffineLineZeroCoordinates
import all Motivic.AlgebraicGeometry.SmoothSiteAffineZeroPoint
import all Motivic.AlgebraicGeometry.SmoothSiteFixedPsiTorus
import all Motivic.AlgebraicGeometry.SmoothSiteNeighborhoodLambdaCylinder
import all Motivic.Cohomology.A1.OriginalPresentationOpenImage
import all Motivic.Cohomology.A1.ZeroNeighborhoodOriginalLifting
import all Motivic.Cohomology.A1.ZeroPointOriginalLifting
import all Motivic.Cohomology.A1.FixedTargetOriginalOverlapLifting
import all Motivic.Cohomology.A1.OriginalPresentationSiteMaps
import all Motivic.Cohomology.A1.RestrictionDifferenceRestriction
import all Motivic.Cohomology.A1.OriginalPresentationOverlapLifting
import all Motivic.Cohomology.A1.OriginalPresentationPolynomialPuncture
import all Motivic.Cohomology.A1.RestrictionDifferenceComposition
import all Motivic.Cohomology.A1.RestrictionDifferenceCartesianComposition
import all Motivic.Cohomology.A1.RestrictionDifferenceMarkedComposition
import all Motivic.Cohomology.A1.OriginalPresentationSecondCorrection
import all Motivic.Cohomology.A1.OriginalPresentationCorrectionSquare
import all Motivic.Cohomology.A1.NeighborhoodCorrectionCoordinates
import all Motivic.Cohomology.A1.OriginalPresentationSecondCylinder
import all Motivic.Cohomology.A1.OriginalPresentationCombinedCorrection
import all Motivic.Cohomology.A1.RestrictionDifferenceIsoAmbient
import all Motivic.Cohomology.A1.PresheafBoundaryPolynomialOverlap
import all Motivic.Cohomology.A1.PresheafBoundaryPolynomialImage
import all Motivic.Cohomology.A1.PresheafContractionBoundaryEpi
import all Motivic.Cohomology.A1.PresheafBoundaryGeneratorEpi
import all Motivic.Cohomology.A1.PresheafBoundaryGeometricImage
import all Motivic.Cohomology.A1.PresheafBoundaryGeometricRefinement
import all Motivic.Cohomology.A1.PuncturedCylinderCoordinates
import all Motivic.Cohomology.A1.PresheafBoundaryCokernel
import all Motivic.Cohomology.A1.PresheafBoundaryGenerators
import all Motivic.Cohomology.A1.PresheafContractionBoundary
import all Motivic.Cohomology.A1.PresheafContractionBoundaryRepresentatives
import all Motivic.Cohomology.A1.PresheafBoundaryLaurentImage
import all Motivic.Cohomology.A1.PresheafBoundaryLiftingRelation
import all Motivic.Cohomology.A1.PresheafBoundaryRefinementImage
import Lean.Util.CollectAxioms
import Batteries.Tactic.Lint

/-! # The original-presheaf canonical boundary from its constructed corrections

The terminal consumer has only the original homotopy-invariance hypothesis.
Its production proof constructs the presentation, both signed corrections,
whole-zero maps and actual open-image cover; no lifting family is supplied.
-/

set_option linter.hashCommand false
public noncomputable section

open CategoryTheory AlgebraicGeometry Motivic Opposite
open AlgebraicGeometry.RelativeProjectiveLine
open AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation
open Motivic.SmoothSiteAffineCoordinates Motivic.PresheafWithTransfers

universe v u

namespace MotivicTest.OriginalPresheafBoundaryLifting

variable {k : Type u} [Field k]

example
    (P : PresheafWithTransfers.{v} k) (hP : P.IsA1Invariant)
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (b : Spec (.of R) ⟶ Spec (.of k)) [Smooth b]
    (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme]
    (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)
    (s : Spec (.of R)) :
    ∃ r : R, s ∈ PrimeSpectrum.basicOpen r ∧
      ∀ d : sections P (Cor.mk (neighborhoodCommonSite k R b V 1)),
      ∃ a : sections P (Cor.mk (neighborhoodPsiSite k R b r)),
      ∃ c : sections P (Cor.mk (neighborhoodLambdaSite k R b V r)),
        ((toPresheaf k).obj P).map (neighborhoodPencilBeta k R b V r).op a -
          ((toPresheaf k).obj P).map (neighborhoodPencilAlpha k R b V r).op c =
        ((toPresheaf k).obj P).map (neighborhoodOriginalRestriction R V k b r).op d :=
  exists_zeroNeighborhood_original_lifting P hP R b V hV s

example
    (P : PresheafWithTransfers.{u + 1} k)
    {O₁ O₂ O T₁ T₂ T A₁ A₂ D : SmoothSite (Spec (.of k))}
    {φ₁ : O₁ ⟶ D} {β₁ : O₁ ⟶ A₁} {α₁ : O₁ ⟶ T₁}
    {φ₂ : O₂ ⟶ A₁} {β₂ : O₂ ⟶ A₂} {α₂ : O₂ ⟶ T₂}
    (h₁ : P.HasRestrictionDifferenceLifting φ₁ β₁ α₁)
    (h₂ : P.HasRestrictionDifferenceLifting φ₂ β₂ α₂)
    (f : O ⟶ O₁) (g : O ⟶ O₂) (hfg : f ≫ β₁ = g ≫ φ₂)
    (α : O ⟶ T) (c₁ : T ⟶ T₁) (c₂ : T ⟶ T₂)
    (hc₁ : α ≫ c₁ = f ≫ α₁) (hc₂ : α ≫ c₂ = g ≫ α₂) :
    P.HasRestrictionDifferenceLifting (f ≫ φ₁) (g ≫ β₂) α :=
  HasRestrictionDifferenceLifting.comp P h₁ h₂ f g hfg α c₁ c₂ hc₁ hc₂


/-- The actual original-presheaf map is epimorphic without a lifting-family input. -/
theorem original_presheaf_canonical_epi [Infinite k]
    (X : SmoothSite (Spec (.of k))) (P : PresheafWithTransfers.{u + 1} k)
    (hP : P.IsA1Invariant) :
    Epi (FiniteEtaleSite.OriginalPresheaf.contractionToBoundary X P) :=
  FiniteEtaleSite.OriginalPresheaf.contractionToBoundary_epi X P hP

/-- The explicit comparison transfers the constructed Epi to the old canonical
sheaf map, and its independently proved Mono makes that same map invertible. -/
theorem original_sheaf_canonical_iso [Infinite k]
    (X : SmoothSite (Spec (.of k))) (F : SheafWithTransfers.{u + 1} k)
    (hF : F.obj.IsA1Invariant) :
    IsIso (FiniteEtaleSite.contractionToBoundary X F hF) := by
  let := original_presheaf_canonical_epi X F.obj hF
  let : Epi ((FiniteEtaleSite.OriginalPresheaf.contractionSheafIso X F hF).hom ≫
      FiniteEtaleSite.contractionToBoundary X F hF) := by
    rw [← FiniteEtaleSite.OriginalPresheaf.contractionToBoundary_sheafIso]
    infer_instance
  let : Epi (FiniteEtaleSite.contractionToBoundary X F hF) :=
    epi_of_epi (FiniteEtaleSite.OriginalPresheaf.contractionSheafIso X F hF).hom _
  let := FiniteEtaleSite.contractionToBoundary_mono X F hF
  exact isIso_of_mono_of_epi _

open Lean in
run_cmd do
  for name in #[``original_presheaf_canonical_epi, ``original_sheaf_canonical_iso,
      ``exists_zeroNeighborhood_original_lifting] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Constructed original-presheaf boundary Epi: standard foundations only."

open Lean Batteries.Tactic.Lint in
run_cmd do
  let env ← getEnv
  let sourceModules := #[`Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.NeighborhoodPunctureIdentification,
    `Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.NeighborhoodPunctureBaseChange,
    `Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.NeighborhoodOriginalAmbientMaps,
    `Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.PolynomialZeroOriginalEtalePresentation,
    `Motivic.AlgebraicGeometry.Sites.FiniteEtaleJacobsonOpenCover,
    `Motivic.AlgebraicGeometry.Sites.FiniteEtaleSmoothNeighborhood,
    `Motivic.AlgebraicGeometry.SmoothSiteAffineLineZeroCoordinates,
    `Motivic.AlgebraicGeometry.SmoothSiteAffineZeroPoint,
    `Motivic.AlgebraicGeometry.SmoothSiteFixedPsiTorus,
    `Motivic.AlgebraicGeometry.SmoothSiteNeighborhoodLambdaCylinder]
  let modules := env.header.moduleNames.map (sourceModules.contains ·)
  let declarations := env.constants.map₁.fold
    (init := ← Lean.Elab.Command.liftCoreM getDeclsInCurrModule) fun declarations name _ =>
      if modules[env.const2ModIdx[name]?.get!]! then declarations.push name else declarations
  unless declarations.size ≥ sourceModules.size do
    throwError "The original boundary source declarations are missing from this lint."
  let linters ← Lean.Elab.Command.liftCoreM (getChecks true none none)
  unless !linters.isEmpty do
    throwError "No declaration linters were selected."
  let results ← Lean.Elab.Command.liftCoreM <|
    Lean.withExporting (isExporting := false) (lintCore declarations linters)
  for (linter, findings) in results do
    for (name, message) in findings.toArray do
      throwError "{linter.name}: {name}: {message}"
  logInfo m!"Original boundary source group: {declarations.size} declarations passed lint."

open Lean Batteries.Tactic.Lint in
run_cmd do
  let env ← getEnv
  let sourceModules := #[`Motivic.Cohomology.A1.OriginalPresentationOpenImage,
    `Motivic.Cohomology.A1.ZeroNeighborhoodOriginalLifting,
    `Motivic.Cohomology.A1.ZeroPointOriginalLifting,
    `Motivic.Cohomology.A1.FixedTargetOriginalOverlapLifting,
    `Motivic.Cohomology.A1.OriginalPresentationSiteMaps,
    `Motivic.Cohomology.A1.RestrictionDifferenceRestriction,
    `Motivic.Cohomology.A1.OriginalPresentationOverlapLifting,
    `Motivic.Cohomology.A1.OriginalPresentationPolynomialPuncture,
    `Motivic.Cohomology.A1.RestrictionDifferenceComposition,
    `Motivic.Cohomology.A1.RestrictionDifferenceCartesianComposition,
    `Motivic.Cohomology.A1.RestrictionDifferenceMarkedComposition]
  let modules := env.header.moduleNames.map (sourceModules.contains ·)
  let declarations := env.constants.map₁.fold
    (init := ← Lean.Elab.Command.liftCoreM getDeclsInCurrModule) fun declarations name _ =>
      if modules[env.const2ModIdx[name]?.get!]! then declarations.push name else declarations
  unless declarations.size ≥ sourceModules.size do
    throwError "The original boundary source declarations are missing from this lint."
  let linters ← Lean.Elab.Command.liftCoreM (getChecks true none none)
  unless !linters.isEmpty do
    throwError "No declaration linters were selected."
  let results ← Lean.Elab.Command.liftCoreM <|
    Lean.withExporting (isExporting := false) (lintCore declarations linters)
  for (linter, findings) in results do
    for (name, message) in findings.toArray do
      throwError "{linter.name}: {name}: {message}"
  logInfo m!"Original boundary source group: {declarations.size} declarations passed lint."

open Lean Batteries.Tactic.Lint in
run_cmd do
  let env ← getEnv
  let sourceModules := #[`Motivic.Cohomology.A1.OriginalPresentationSecondCorrection,
    `Motivic.Cohomology.A1.OriginalPresentationCorrectionSquare,
    `Motivic.Cohomology.A1.NeighborhoodCorrectionCoordinates,
    `Motivic.Cohomology.A1.OriginalPresentationSecondCylinder,
    `Motivic.Cohomology.A1.OriginalPresentationCombinedCorrection,
    `Motivic.Cohomology.A1.RestrictionDifferenceIsoAmbient,
    `Motivic.Cohomology.A1.PresheafBoundaryPolynomialOverlap,
    `Motivic.Cohomology.A1.PresheafBoundaryPolynomialImage,
    `Motivic.Cohomology.A1.PresheafContractionBoundaryEpi,
    `Motivic.Cohomology.A1.PresheafBoundaryGeneratorEpi]
  let modules := env.header.moduleNames.map (sourceModules.contains ·)
  let declarations := env.constants.map₁.fold
    (init := ← Lean.Elab.Command.liftCoreM getDeclsInCurrModule) fun declarations name _ =>
      if modules[env.const2ModIdx[name]?.get!]! then declarations.push name else declarations
  unless declarations.size ≥ sourceModules.size do
    throwError "The original boundary source declarations are missing from this lint."
  let linters ← Lean.Elab.Command.liftCoreM (getChecks true none none)
  unless !linters.isEmpty do
    throwError "No declaration linters were selected."
  let results ← Lean.Elab.Command.liftCoreM <|
    Lean.withExporting (isExporting := false) (lintCore declarations linters)
  for (linter, findings) in results do
    for (name, message) in findings.toArray do
      throwError "{linter.name}: {name}: {message}"
  logInfo m!"Original boundary source group: {declarations.size} declarations passed lint."

open Lean Batteries.Tactic.Lint in
run_cmd do
  let env ← getEnv
  let sourceModules := #[`Motivic.Cohomology.A1.PresheafBoundaryGeometricImage,
    `Motivic.Cohomology.A1.PresheafBoundaryGeometricRefinement,
    `Motivic.Cohomology.A1.PuncturedCylinderCoordinates,
    `Motivic.Cohomology.A1.PresheafBoundaryCokernel,
    `Motivic.Cohomology.A1.PresheafBoundaryGenerators,
    `Motivic.Cohomology.A1.PresheafContractionBoundary,
    `Motivic.Cohomology.A1.PresheafContractionBoundaryRepresentatives,
    `Motivic.Cohomology.A1.PresheafBoundaryLaurentImage,
    `Motivic.Cohomology.A1.PresheafBoundaryLiftingRelation,
    `Motivic.Cohomology.A1.PresheafBoundaryRefinementImage]
  let modules := env.header.moduleNames.map (sourceModules.contains ·)
  let declarations := env.constants.map₁.fold
    (init := ← Lean.Elab.Command.liftCoreM getDeclsInCurrModule) fun declarations name _ =>
      if modules[env.const2ModIdx[name]?.get!]! then declarations.push name else declarations
  unless declarations.size ≥ sourceModules.size do
    throwError "The original boundary source declarations are missing from this lint."
  let linters ← Lean.Elab.Command.liftCoreM (getChecks true none none)
  unless !linters.isEmpty do
    throwError "No declaration linters were selected."
  let results ← Lean.Elab.Command.liftCoreM <|
    Lean.withExporting (isExporting := false) (lintCore declarations linters)
  for (linter, findings) in results do
    for (name, message) in findings.toArray do
      throwError "{linter.name}: {name}: {message}"
  logInfo m!"Original boundary source group: {declarations.size} declarations passed lint."

end MotivicTest.OriginalPresheafBoundaryLifting
