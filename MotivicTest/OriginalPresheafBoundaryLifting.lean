/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.Boundary.Presheaf.Contraction.Epi
public import Motivic.Cohomology.A1.Boundary.Contraction.SheafComparison
public import Motivic.Cohomology.A1.Boundary.Contraction.Mono
import all Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Retained.Identification
import all Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Retained.BaseChange
import all Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.OriginalAmbientMaps
import all Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.PolynomialZeroOriginalEtalePresentation
import all Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.JacobsonOpenCover
import all Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.SmoothNeighborhood
import all Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Affine.LineZeroCoordinates
import all Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Affine.ZeroPoint
import all Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.PunctureTorus
import all Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.NeighborhoodCylinder
import all Motivic.Cohomology.A1.LocalVanishing.Presentation.OpenImage
import all Motivic.Cohomology.A1.LocalVanishing.ZeroNeighborhood.OriginalLifting
import all Motivic.Cohomology.A1.LocalVanishing.ZeroNeighborhood.OriginalPointLifting
import all Motivic.Cohomology.A1.LocalVanishing.FixedTarget.OriginalOverlapLifting
import all Motivic.Cohomology.A1.LocalVanishing.Presentation.SiteMaps
import all Motivic.Cohomology.A1.Boundary.RestrictionDifference.Restriction
import all Motivic.Cohomology.A1.LocalVanishing.Presentation.OverlapLifting
import all Motivic.Cohomology.A1.LocalVanishing.Presentation.PolynomialPuncture
import all Motivic.Cohomology.A1.Boundary.RestrictionDifference.Composition
import all Motivic.Cohomology.A1.Boundary.RestrictionDifference.CartesianComposition
import all Motivic.Cohomology.A1.Boundary.RestrictionDifference.MarkedComposition
import all Motivic.Cohomology.A1.LocalVanishing.Presentation.SecondCorrection
import all Motivic.Cohomology.A1.LocalVanishing.Presentation.CorrectionSquare
import all Motivic.Cohomology.A1.LocalVanishing.NeighborhoodCorrectionCoordinates
import all Motivic.Cohomology.A1.LocalVanishing.Presentation.SecondCylinder
import all Motivic.Cohomology.A1.LocalVanishing.Presentation.CombinedCorrection
import all Motivic.Cohomology.A1.Boundary.RestrictionDifference.IsoAmbient
import all Motivic.Cohomology.A1.Boundary.Presheaf.PolynomialOverlap
import all Motivic.Cohomology.A1.Boundary.Presheaf.PolynomialImage
import all Motivic.Cohomology.A1.Boundary.Presheaf.Contraction.Epi
import all Motivic.Cohomology.A1.Boundary.Presheaf.GeneratorEpi
import all Motivic.Cohomology.A1.Boundary.Presheaf.GeometricImage
import all Motivic.Cohomology.A1.Boundary.Presheaf.GeometricRefinement
import all Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.PuncturedCoordinates
import all Motivic.Cohomology.A1.Boundary.Presheaf.Cokernel
import all Motivic.Cohomology.A1.Boundary.Presheaf.Generators
import all Motivic.Cohomology.A1.Boundary.Presheaf.Contraction.Basic
import all Motivic.Cohomology.A1.Boundary.Presheaf.Contraction.Representatives
import all Motivic.Cohomology.A1.Boundary.Presheaf.LaurentImage
import all Motivic.Cohomology.A1.Boundary.Presheaf.LiftingRelation
import all Motivic.Cohomology.A1.Boundary.Presheaf.RefinementImage
import Lean.Util.CollectAxioms
import Batteries.Tactic.Lint

/-! # The original-presheaf canonical boundary from its constructed corrections

The terminal consumer has only the original homotopy-invariance hypothesis.
Its production proof constructs the presentation, both signed corrections,
whole-zero maps and actual open-image cover; no lifting family is supplied.
-/

set_option linter.hashCommand false
public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory AlgebraicGeometry Motivic Opposite
open AlgebraicGeometry.RelativeProjectiveLine
open AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation
open _root_.AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
open _root_.AlgebraicSimplex
open _root_.Motivic.PresheafWithTransfers

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
  let sourceModules :=
      #[`Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Retained.Identification,
    `Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Retained.BaseChange,
    `Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.OriginalAmbientMaps,
    (`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic).str
      "PolynomialZeroOriginalEtalePresentation",
    `Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.JacobsonOpenCover,
    `Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.SmoothNeighborhood,
    `Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Affine.LineZeroCoordinates,
    `Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Affine.ZeroPoint,
    `Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.PunctureTorus,
    `Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.NeighborhoodCylinder]
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
  let sourceModules := #[`Motivic.Cohomology.A1.LocalVanishing.Presentation.OpenImage,
    `Motivic.Cohomology.A1.LocalVanishing.ZeroNeighborhood.OriginalLifting,
    `Motivic.Cohomology.A1.LocalVanishing.ZeroNeighborhood.OriginalPointLifting,
    `Motivic.Cohomology.A1.LocalVanishing.FixedTarget.OriginalOverlapLifting,
    `Motivic.Cohomology.A1.LocalVanishing.Presentation.SiteMaps,
    `Motivic.Cohomology.A1.Boundary.RestrictionDifference.Restriction,
    `Motivic.Cohomology.A1.LocalVanishing.Presentation.OverlapLifting,
    `Motivic.Cohomology.A1.LocalVanishing.Presentation.PolynomialPuncture,
    `Motivic.Cohomology.A1.Boundary.RestrictionDifference.Composition,
    `Motivic.Cohomology.A1.Boundary.RestrictionDifference.CartesianComposition,
    `Motivic.Cohomology.A1.Boundary.RestrictionDifference.MarkedComposition]
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
  let sourceModules := #[`Motivic.Cohomology.A1.LocalVanishing.Presentation.SecondCorrection,
    `Motivic.Cohomology.A1.LocalVanishing.Presentation.CorrectionSquare,
    `Motivic.Cohomology.A1.LocalVanishing.NeighborhoodCorrectionCoordinates,
    `Motivic.Cohomology.A1.LocalVanishing.Presentation.SecondCylinder,
    `Motivic.Cohomology.A1.LocalVanishing.Presentation.CombinedCorrection,
    `Motivic.Cohomology.A1.Boundary.RestrictionDifference.IsoAmbient,
    `Motivic.Cohomology.A1.Boundary.Presheaf.PolynomialOverlap,
    `Motivic.Cohomology.A1.Boundary.Presheaf.PolynomialImage,
    `Motivic.Cohomology.A1.Boundary.Presheaf.Contraction.Epi,
    `Motivic.Cohomology.A1.Boundary.Presheaf.GeneratorEpi]
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
  let sourceModules := #[`Motivic.Cohomology.A1.Boundary.Presheaf.GeometricImage,
    `Motivic.Cohomology.A1.Boundary.Presheaf.GeometricRefinement,
    `Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.PuncturedCoordinates,
    `Motivic.Cohomology.A1.Boundary.Presheaf.Cokernel,
    `Motivic.Cohomology.A1.Boundary.Presheaf.Generators,
    `Motivic.Cohomology.A1.Boundary.Presheaf.Contraction.Basic,
    `Motivic.Cohomology.A1.Boundary.Presheaf.Contraction.Representatives,
    `Motivic.Cohomology.A1.Boundary.Presheaf.LaurentImage,
    `Motivic.Cohomology.A1.Boundary.Presheaf.LiftingRelation,
    `Motivic.Cohomology.A1.Boundary.Presheaf.RefinementImage]
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
