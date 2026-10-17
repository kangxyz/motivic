/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.DiagonalMilnorBoundaryDescent
public import Lean.Util.CollectAxioms

/-! The actual all-weight boundary descent, retaining the original homology and Milnor group. -/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Motivic
open Motivic.DiagonalMilnorBoundaryDescent Motivic.DiagonalTopDegree
universe w u
namespace MotivicTest.DiagonalMilnorBoundaryDescent
variable (k : Type u) [Field k] [CharZero k]

/-- No unramifiedness, branch-matching, or boundary-vanishing premise is supplied. -/
theorem actual_boundary_norm_zero (q : ℕ) (s : chains k q 1) :
    DiagonalBoundaryEvaluation.degreeZeroNorm k q (boundary k q s) = 0 :=
  degreeZeroNorm_boundary k q s

/-- The full original signed point-cycle formula survives actual homology descent. -/
theorem actual_cycle_class_norm (q : ℕ)
    (α : point k ⟶ DiagonalCycleSymbols.target k q) :
    rawNorm k q (DiagonalCycleSymbols.cycleClass k q α) =
      DiagonalPointNorm.cycleValue k q α := rawNorm_cycleClass k q α

open Lean in
run_cmd do
  for name in #[``actual_boundary_norm_zero, ``actual_cycle_class_norm,
      ``cycleValue_endpoint_eq, ``degreeZeroNorm_boundary, ``quotientNorm,
      ``rawTermNorm, ``rawTermNorm_differential, ``rawNorm,
      ``rawNorm_singularClass, ``rawNorm_cycleClass,
      ``rawNorm_graphSymbol,
      ``motivicNorm, ``motivicNorm_comparison] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual all-weight diagonal boundary descent: standard foundations only."

end MotivicTest.DiagonalMilnorBoundaryDescent
