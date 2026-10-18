/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.PointedCylinderPositiveChartVanishing
import all Motivic.AlgebraicGeometry.Sites.FiniteEtaleOrdinarySupportNaturality
import all Motivic.AlgebraicGeometry.Sites.FiniteEtaleSplitClosedPresheafFiber
import all Motivic.Cohomology.A1.ContractionChartSupport
import all Motivic.Cohomology.A1.PointedCylinderPositiveSupport
import all Motivic.Cohomology.A1.PointedCylinderPositiveChartVanishing
public import Lean.Util.CollectAxioms
public import Batteries.Tactic.Lint

/-! # Actual positive cylinder germs in the coefficient kernel

This consumer retains the full field-valued mark and original BASE refinement.
Only lower-degree homotopy invariance for the contraction is assumed. Canonical
boundary Epi is proved internally; puncture-cohomology injectivity is not claimed.
-/

public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open Motivic Motivic.FiniteEtaleSite
universe u
namespace MotivicTest.PointedCylinderPositiveChartVanishing

local instance positiveKernelTestHasExt (S : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives _

variable {k : Type u} [Field k] [Infinite k]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  (X : SmoothSite (Spec (.of k))) {E U : SmoothSite (Spec (.of k))}
  (b : E ⟶ SmoothSite.a1Cylinder (.of k) X) [Etale b.left]
  (F : SheafWithTransfers.{u + 1} k) (j : U ⟶ E)
  (q : U ⟶ SmoothSite.torusCylinder (.of k) X)
  (hj : IsPullback q j (SmoothSite.contractionOpen (.of k) X) b)
  (d : X ⟶ E) (hd : IsPullback d (𝟙 X) b (SmoothSite.a1Section (.of k) X 0))
  (hF : F.obj.IsA1Invariant)
  (K : Type u) [Field K] (c : Spec (.of K) ⟶ X.left) (n : ℕ)
  (hH : (SheafCohomology.withTransfers k (SheafWithTransfers.contraction F hF)
    (n + 1)).IsA1Invariant)

local notation "G" => Functor.obj (SheafWithTransfers.toSheaf k) F
local notation "E₁" => SmoothSite.a1Cylinder (CommRingCat.of k) E
local notation "πE" => SmoothSite.a1Projection (CommRingCat.of k) E
local notation "j₁" => SmoothSite.a1Map (CommRingCat.of k) j
local notation "Φ" => relativeFieldPoint (c ≫ d.left) K (𝟙 _)

include hj hd hF hH in
/-- The original degree `n + 2` cylinder germ dies in the coefficient kernel,
using lower-degree HI only for the unchanged contraction coefficient. The
canonical boundary epimorphism is the proved one, not a supplied input. -/
theorem original_positive_coefficient_kernel_germ_zero
    (V : (Φ).fiber.Elements)
    (s : (pointedCylinderValues (.of k) Φ
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) G (n + 2))
      (pointedBase (.of k) Φ)).obj (op V))
    (hs : ((pointedCylinderOrdinaryIso (.of k) E Φ G (n + 2)).hom.app (op V) s).comp
      (Ext.mk₀ (restrictionToDirectImage G j₁)) (add_zero (n + 2)) = 0) :
    colimit.ι (pointedCylinderValues (.of k) Φ
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) G (n + 2))
      (pointedBase (.of k) Φ)) (op V) s = 0 := by
  exact pointedCylinder_positive_germ_zero_of_chart_coefficient_kernel
    X b F j q hj d hd hF K c n hH V s hs

open Lean Batteries.Tactic.Lint in
run_cmd do
  let env ← getEnv
  let sourceModules := #[`Motivic.AlgebraicGeometry.Sites.FiniteEtaleOrdinarySupportNaturality,
    `Motivic.AlgebraicGeometry.Sites.FiniteEtaleSplitClosedPresheafFiber,
    `Motivic.Cohomology.A1.ContractionChartSupport,
    `Motivic.Cohomology.A1.PointedCylinderPositiveSupport,
    `Motivic.Cohomology.A1.PointedCylinderPositiveChartVanishing]
  let modules := env.header.moduleNames.map (sourceModules.contains ·)
  let declarations := env.constants.map₁.fold
    (init := ← Lean.Elab.Command.liftCoreM getDeclsInCurrModule) fun declarations name _ =>
      if modules[env.const2ModIdx[name]?.get!]! then declarations.push name else declarations
  unless declarations.size ≥ 25 do
    throwError "The actual support, BASE comparison, and original germ declarations are missing."
  for name in declarations do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
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
  logInfo m!"Positive coefficient-kernel germ: {declarations.size} declarations passed lint and std3."

end MotivicTest.PointedCylinderPositiveChartVanishing
