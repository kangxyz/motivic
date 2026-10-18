/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.BoundaryFramedDivisorPairs
import all Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.BoundaryFramed
import all Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.BoundaryFramedTensor
import all Motivic.Aglib.AlgebraicGeometry.RelativeCurve.BoundaryFramedDivisorPairs
public import Lean.Util.CollectAxioms
public import Batteries.Tactic.Lint

/-! # A geometric consumer of boundary-framed divisor pairs

The consumer obtains the actual finite-flat zero schemes from the section producer,
then checks that forgetting the proved framed relation gives the original Picard
addition. No section, finite-flat witness or class-comparison premise is supplied.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace MotivicTest.BoundaryFramedDivisorPairs

/-- The geometric producer and framed comparison recover ordinary Picard addition
for the same sections whose entire zero schemes are finite flat. -/
theorem exists_pair_with_original_picard_relation
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))
    {C W U : Scheme.{u}} [IsLocallyNoetherian C]
    (a : C ⟶ ProjectiveSpace R ι) [IsFinite a]
    (z : W ⟶ C) [IsClosedImmersion z]
    (eQ : ∀ d : ℕ, (moduleTensorLeftFunctor W
      ((Scheme.Modules.pullback z).obj ((Scheme.Modules.pullback a).obj (twistingSheaf R ι (d : ℤ))))).obj
        ((Scheme.Modules.pullback z).obj (SheafOfModules.unit C.ringCatSheaf)) ≅
          SheafOfModules.unit W.ringCatSheaf)
    (j : U ⟶ C) [IsOpenImmersion j] [U.IsQuasiAffine]
    [SmoothOfRelativeDimension 1 (j ≫ a ≫ toSpec R ι)]
    (hcover : ∀ x : C, x ∈ Set.range j ∨ x ∈ Set.range z)
    (M : BoundaryFramedLineBundle z) :
    ∃ d : ℕ,
      let T := pullbackLineBundle a (twistingLineBundle R ι (d : ℤ))
      ∃ s : SheafOfModules.unit C.ringCatSheaf ⟶ (tensorLineBundle C T M.lineBundle).val,
      ∃ t : SheafOfModules.unit C.ringCatSheaf ⟶ T.val,
      ∃ hs : IsIso (pullbackSectionMap z s), ∃ ht : IsIso (pullbackSectionMap z t),
        BoundaryFramedLineBundle.classOf
            (@BoundaryFramedLineBundle.ofSection _ _ z (tensorLineBundle C T M.lineBundle) s hs) =
          BoundaryFramedLineBundle.tensorClass
            (BoundaryFramedLineBundle.classOf (@BoundaryFramedLineBundle.ofSection _ _ z T t ht))
            (BoundaryFramedLineBundle.classOf M) ∧
        Scheme.CoherentGraph.SectionDivisorFiniteFlat (a ≫ toSpec R ι) j
          (tensorLineBundle C T M.lineBundle) s ∧
        Scheme.CoherentGraph.SectionDivisorFiniteFlat (a ≫ toSpec R ι) j T t ∧
        classOf C (tensorLineBundle C T M.lineBundle) =
          classOf C T + classOf C M.lineBundle := by
  obtain ⟨B, hB⟩ := Scheme.CoherentGraph.exists_boundaryFramed_divisor_pair
    R ι n e a z eQ j hcover M
  obtain ⟨s, t, hs, ht, _, hsff, htff, hc⟩ := hB B le_rfl
  refine ⟨B, s, t, hs, ht, hc, hsff, htff, ?_⟩
  have hf := congrArg BoundaryFramedLineBundle.forget hc
  simpa only [BoundaryFramedLineBundle.forget_tensorClass,
    BoundaryFramedLineBundle.forget_classOf, BoundaryFramedLineBundle.ofSection] using hf

open Lean Batteries.Tactic.Lint in
run_cmd do
  let env ← getEnv
  let sourceModules := #[
    `Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.BoundaryFramed,
    `Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.BoundaryFramedTensor,
    `Motivic.Aglib.AlgebraicGeometry.RelativeCurve.BoundaryFramedDivisorPairs]
  let modules := env.header.moduleNames.map (sourceModules.contains ·)
  let declarations := env.constants.map₁.fold
    (init := ← Lean.Elab.Command.liftCoreM getDeclsInCurrModule) fun declarations name _ =>
      if modules[env.const2ModIdx[name]?.get!]! then declarations.push name else declarations
  unless declarations.size ≥ 25 do
    throwError "Boundary-framed declarations are missing from the exact-scope audit."
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
  logInfo m!"All {declarations.size} boundary-framed declarations: lint and standard axioms passed."

end MotivicTest.BoundaryFramedDivisorPairs
