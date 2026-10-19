/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Cartier.BoundaryZero
public import Motivic.Cohomology.A1.Boundary.Presheaf.OpenSupport
import all Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Cartier.CylinderComparison
import all Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Cartier.PunctureComparison
import all Motivic.Cohomology.A1.Boundary.Presheaf.CoefficientIso
import all Motivic.Cohomology.A1.Boundary.Presheaf.SmoothCartierZero
import all Motivic.Cohomology.Cartier.BoundaryZero
import all Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Point.InverseImageComposition
import all Motivic.Cohomology.A1.Boundary.Presheaf.PointComparison
import all Motivic.Cohomology.A1.Boundary.Presheaf.OpenZero
import all Motivic.Cohomology.A1.Boundary.Presheaf.OpenSupport
import all Motivic.Cohomology.A1.Boundary.Presheaf.EtaleLocalization
import all Motivic.Cohomology.A1.Boundary.Presheaf.EtaleExcision
public import Lean.Util.CollectAxioms
public import Batteries.Tactic.Lint

/-! # The actual Cartier boundary-zero consumer with explicit original boundary Epi -/

public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open Scheme.Modules Scheme.Modules.Invertible

universe u

namespace MotivicTest.SheafCohomologyCartierBoundaryZero

variable (k : Type u) [Field k] [Infinite k]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  (F : SheafWithTransfers.{u + 1} k) (n : ℕ)
  (hP : (SheafCohomology.withTransfers k F (n + 1)).IsA1Invariant)
  (hE : ∀ X : SmoothSite (Spec (.of k)),
    Epi (FiniteEtaleSite.OriginalPresheaf.contractionToBoundary X
      (SheafCohomology.withTransfers k F (n + 1))))

include hP hE

example {U Y : SmoothSite (Spec (.of k))} (j : U ⟶ Y) [IsOpenImmersion j.left]
    {Z : Scheme.{u}} (i : Z ⟶ Y.left) [IsClosedImmersion i] [Smooth (i ≫ Y.hom)]
    (hI : IsLocallyRankOne Y.left (Scheme.Hom.idealModule i))
    (hcomp : Set.range i = (Set.range j.left)ᶜ) :
    IsZero ((_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.inverseImage i).obj
        (FiniteEtaleSite.presheafBoundaryAmbient
      (_root_.CategoryTheory.Sheaf.LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k)))
        ((SheafWithTransfers.toSheaf k).obj F) (n + 1)) j)) :=
  SheafCohomology.isZero_cartierBoundary_succ_of_epi k F n hP hE j i hI hcomp

/-- Actual positive open direct image vanishes under the retained original Epi input. -/
theorem higherDirectImage_isZero_of_original_epi
    {U Y : SmoothSite (Spec (.of k))} (j : U ⟶ Y) [IsOpenImmersion j.left]
    {Z : Scheme.{u}} (i : Z ⟶ Y.left) [IsClosedImmersion i] [Smooth (i ≫ Y.hom)]
    (hI : IsLocallyRankOne Y.left (Scheme.Hom.idealModule i))
    (hcomp : Set.range i = (Set.range j.left)ᶜ) :
    IsZero (((_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.directImage
        j.left).rightDerived (n + 1)).obj
      ((_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.restrict U AddCommGrpCat).obj
        ((SheafWithTransfers.toSheaf k).obj F))) :=
  FiniteEtaleSite.higherDirectImage_isZero_of_positiveBoundary_zero (.of k) j i hcomp
    ((SheafWithTransfers.toSheaf k).obj F) n
    (SheafCohomology.isZero_cartierBoundary_succ_of_epi k F n hP hE j i hI hcomp)

open Lean in
run_cmd do
  for name in #[``higherDirectImage_isZero_of_original_epi,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.exists_cartier_cylinder_comparison,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.exists_cartier_puncture_comparison,
      ``FiniteEtaleSite.presheafBoundaryAmbientCoefficientIso_projection,
      ``FiniteEtaleSite.etaleSheafificationIso_unit,
      ``FiniteEtaleSite.presheafNeighborhoodQuotientEtaleIso_π,
      ``FiniteEtaleSite.presheafBoundaryAmbientEtaleIso_projection,
      ``FiniteEtaleSite.positiveBoundaryPointHigherImageIso_projection,
      ``FiniteEtaleSite.isZero_presheafBoundary_of_smooth_cartier,
      ``SheafCohomology.isZero_zeroSectionBoundary_succ_of_epi,
      ``SheafCohomology.isZero_cartierBoundary_succ_of_epi] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual Cartier boundary zero with explicit Epi input: standard foundations only."

open Lean Batteries.Tactic.Lint in
run_cmd do
  let env ← getEnv
  let sourceModules := #[`Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Cartier.CylinderComparison,
    `Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Cartier.PunctureComparison,
    `Motivic.Cohomology.A1.Boundary.Presheaf.CoefficientIso,
    `Motivic.Cohomology.A1.Boundary.Presheaf.SmoothCartierZero,
    `Motivic.Cohomology.Cartier.BoundaryZero,
    `Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Point.InverseImageComposition,
    `Motivic.Cohomology.A1.Boundary.Presheaf.PointComparison,
    `Motivic.Cohomology.A1.Boundary.Presheaf.OpenZero,
    `Motivic.Cohomology.A1.Boundary.Presheaf.OpenSupport,
    `Motivic.Cohomology.A1.Boundary.Presheaf.EtaleLocalization,
    `Motivic.Cohomology.A1.Boundary.Presheaf.EtaleExcision]
  let modules := env.header.moduleNames.map (sourceModules.contains ·)
  let declarations := env.constants.map₁.fold
    (init := ← Lean.Elab.Command.liftCoreM getDeclsInCurrModule) fun declarations name _ =>
      if modules[env.const2ModIdx[name]?.get!]! then declarations.push name else declarations
  unless declarations.size ≥ 39 do
    throwError "The actual Cartier/excision/point declarations are missing from this lint."
  let linters ← Lean.Elab.Command.liftCoreM (getChecks true none none)
  unless !linters.isEmpty do
    throwError "No declaration linters were selected."
  let results ← Lean.Elab.Command.liftCoreM <|
    Lean.withExporting (isExporting := false) (lintCore declarations linters)
  for (linter, findings) in results do
    for (name, message) in findings.toArray do
      throwError "{linter.name}: {name}: {message}"
  logInfo m!"Actual Cartier boundary zero: {declarations.size} declarations passed lint."

end MotivicTest.SheafCohomologyCartierBoundaryZero
