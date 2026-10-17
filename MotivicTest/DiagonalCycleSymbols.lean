/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.DiagonalCycleSymbols
public import Lean.Util.CollectAxioms

/-!
# Consumers of actual all-weight rational symbols

These checks retain the full rational tuple and test arbitrary positions,
identity coordinates, actual endpoint relations, and signed representatives.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Motivic Motivic.DiagonalTopDegree
open Motivic.DiagonalCycleSymbols

universe u

namespace MotivicTest.DiagonalCycleSymbols

variable (k : Type u) [Field k]

/-- Every position of an arbitrary rational tuple is multiplicatively additive. -/
theorem actual_coordinate_multilinearity (n : ℕ) (a : Fin n → kˣ) (i : Fin n) (b c : kˣ) :
    graphSymbol k n (Function.update a i (b * c)) =
      graphSymbol k n (Function.update a i b) + graphSymbol k n (Function.update a i c) :=
  graphSymbol_mul k n a i b c

/-- Any coordinate equal to one is killed by the original identity-axis quotient. -/
theorem actual_identity_axis (n : ℕ) (a : Fin n → kˣ) (i : Fin n) (h : a i = 1) :
    graphSymbol k n a = 0 := graphSymbol_one k n a i h

/-- Actual all-weight homology classes retain original signed cycle representatives. -/
theorem actual_signed_representatives (n : ℕ)
    (x : (motivicRawBaseComplex k n).homology n) :
    ∃ α : point k ⟶ target k n, cycleClass k n α = x := cycleClass_surjective k n x

open Lean in
run_cmd do
  for name in #[``target, ``cycleClass, ``singularClass_quotient,
      ``singularClass_face_quotient, ``cycleClass_endpoints, ``cycleClass_axis,
      ``rationalTuple, ``rationalTuple_toBase, ``rationalTuple_axis, ``graphSymbol,
      ``graphSymbol_one, ``varyingCoordinate, ``rationalPoint_varyingCoordinate,
      ``cycleClass_quadratic_postcompose, ``graphSymbol_mul, ``cycleClass_surjective,
      ``actual_coordinate_multilinearity, ``actual_identity_axis,
      ``actual_signed_representatives] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual all-weight rational symbols use only standard foundations."

end MotivicTest.DiagonalCycleSymbols
