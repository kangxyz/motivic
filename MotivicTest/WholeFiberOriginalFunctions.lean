/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.WholeFiberOriginalFunctions
public import Lean

/-! # Audit of the unchanged original-function whole-fiber producer -/
open Lean in
run_cmd do
  for name in #[``QuadraticIncidence.exists_originalFunctions_whole_fiber_independent,
      ``QuadraticIncidence.exists_parameterTuple_whole_fiber_independent,
      ``KaehlerDifferential.residueGeneratorGradient_map_polynomial,
      ``KaehlerDifferential.differential_aeval_generator] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original polynomial functions and whole-fiber independence: standard foundations only."
