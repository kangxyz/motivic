/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Polynomial.BoundaryOneRationalFunctions.Cylinder
public import Lean.Util.CollectAxioms

/-! # Direct audit of actual affine boundary-one rational-function acyclicity -/

@[expose] public noncomputable section

open Polynomial.BoundaryOneRationalFunctions CategoryTheory CategoryTheory.Limits

universe u

namespace MotivicTest.BoundaryOneRationalCylinder

/-- A direct consumer at every degree, including degree zero and the zero ring. -/
theorem actual_affine_all_degree_acyclicity (R : Type u) [CommRing R] (n : ℕ) :
    IsZero ((SingularComplex.obj (algebraicSimplex R) ringPresheaf).homology n) :=
  isZero_homology_algebraicSimplex R n

open Lean in
run_cmd do
  for name in #[``ringPresheaf, ``cylinderInclusion, ``cylinderEvaluation,
      ``cylinderEvaluation_natural, ``cylinderPath, ``cylinderPath_zero,
      ``cylinderPath_face, ``cylinderEvaluation_endpoint, ``cylinderPath_start,
      ``cylinderPath_end, ``isZero_homology_of_interval, ``algebraicSimplex,
      ``algebraicSimplex_interval_zero, ``algebraicSimplex_interval_one,
      ``isZero_homology_algebraicSimplex, ``actual_affine_all_degree_acyclicity] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual affine all-degree acyclicity uses only standard Lean foundations."

end MotivicTest.BoundaryOneRationalCylinder
