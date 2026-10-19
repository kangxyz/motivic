/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.LocalVanishing.DenseOpen.RestrictionMono
import all Motivic.Cohomology.A1.LocalVanishing.DenseOpen.RestrictionMono
import all Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Complement.CartierComplementDense
public import Lean.Util.CollectAxioms
public import Batteries.Tactic.Lint

/-! # Original dense-open coefficient restriction consumers -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace MotivicTest.DenseOpenRestrictionMono
open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open Motivic _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType _root_.Motivic.FiniteEtaleSite

/-- Native Cartier density requires no field, smoothness, or Noetherian premise. -/
theorem actual_cartier_complement_dense {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [IsClosedImmersion i] (hI : IsLocallyRankOne Y (Scheme.Hom.idealModule i)) :
    Dense (Set.range i)ᶜ :=
  i.dense_compl_range_of_isLocallyRankOne hI

variable {k : Type u} [Field k] [Infinite k]
  (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant)

include hF

/-- The actual section and its original graph restriction, not an abstract injection. -/
theorem original_dense_open_section_zero {U Y : SmoothSite (Spec (.of k))}
    (j : U ⟶ Y) [IsOpenImmersion j.left] (hj : DenseRange j.left)
    (s : F.obj.sections (Cor.mk Y))
    (hs : F.obj.transfer ((Cor.graphFunctor k).map j) s = 0) : s = 0 :=
  F.section_eq_zero_of_dense_open j hj hF s hs

/-- The genuine original coefficient-to-open-direct-image morphism is monic.
No positive ordinary-cohomology injectivity follows merely from this statement. -/
theorem original_cartier_coefficient_mono {U Y : SmoothSite (Spec (.of k))}
    (j : U ⟶ Y) [IsOpenImmersion j.left] {Z : Scheme.{u}} (i : Z ⟶ Y.left)
    [IsClosedImmersion i] (hI : IsLocallyRankOne Y.left (Scheme.Hom.idealModule i))
    (hcomp : Set.range i = (Set.range j.left)ᶜ) :
    Mono (restrictionToDirectImage ((SheafWithTransfers.toSheaf k).obj F) j) :=
  restrictionToDirectImage_mono_of_cartier j F hF i hI hcomp

open Lean in
run_cmd do
  for name in #[``actual_cartier_complement_dense, ``original_dense_open_section_zero,
      ``original_cartier_coefficient_mono, ``PrimeSpectrum.dense_basicOpen_of_isRegular,
      ``Scheme.Hom.dense_compl_range_of_isLocallyRankOne,
      ``SheafWithTransfers.section_eq_zero_of_dense_open,
      ``restrictionToDirectImage_mono_of_dense, ``restrictionToDirectImage_mono_of_cartier] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual Cartier density and original coefficient restriction: standard axioms only."

open Lean Batteries.Tactic.Lint in
run_cmd do
  let env ← getEnv
  let sourceModules :=
      #[`Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Complement.CartierComplementDense,
    `Motivic.Cohomology.A1.LocalVanishing.DenseOpen.RestrictionMono]
  let modules := env.header.moduleNames.map (sourceModules.contains ·)
  let declarations := env.constants.map₁.fold
    (init := ← Lean.Elab.Command.liftCoreM getDeclsInCurrModule) fun declarations name _ =>
      if modules[env.const2ModIdx[name]?.get!]! then declarations.push name else declarations
  unless declarations.size ≥ 8 do
    throwError
      "The Cartier density and original coefficient declarations are missing from this lint."
  let linters ← Lean.Elab.Command.liftCoreM (getChecks true none none)
  unless !linters.isEmpty do
    throwError "No declaration linters were selected."
  let results ← Lean.Elab.Command.liftCoreM <|
    Lean.withExporting (isExporting := false) (lintCore declarations linters)
  for (linter, findings) in results do
    for (name, message) in findings.toArray do
      throwError "{linter.name}: {name}: {message}"
  logInfo "Cartier density and original coefficient restriction: selected declarations passed lint."

end MotivicTest.DenseOpenRestrictionMono
