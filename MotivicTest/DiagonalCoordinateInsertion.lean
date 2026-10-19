/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Diagonal.CoordinateInsertion
public import Lean.Util.CollectAxioms

/-!
# Consumers of actual fixed-coordinate insertion and the all-weight Steinberg relation

The boundary test is for the original reduced torus differential; the Steinberg
test allows every pair of distinct positions and retains the full rational tuple.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry
open Motivic
open _root_.AlgebraicSimplex
open _root_.Motivic.PresheafWithTransfers
open Motivic.DiagonalTopDegree Motivic.DiagonalCycleSymbols Motivic.DiagonalCoordinateInsertion

universe u

namespace MotivicTest.DiagonalCoordinateInsertion

variable (k : Type u) [Field k]

/-- Actual fixed-coordinate insertion preserves the entire genuine singular boundary. -/
theorem actual_insertion_boundary (q : ℕ) (a : Fin (q + 1) → kˣ)
    (i j : Fin (q + 1)) (hij : i ≠ j) (x : chains k 2 1) :
    (pairInsertion k q a i j hij).hom.app (Opposite.op (Cor.simplexProduct (point k) 0))
      (boundary k 2 x) = boundary k (q + 1)
        ((pairInsertion k q a i j hij).hom.app
          (Opposite.op (Cor.simplexProduct (point k) 1)) x) :=
  coefficientMap_boundary k _ x

/-- The original characteristic-zero weight-two theorem kills actual tuples in all weights. -/
theorem actual_steinberg [CharZero k] (q : ℕ) (a : Fin q → kˣ)
    (i j : Fin q) (hij : i ≠ j) (hab : (a i : k) + (a j : k) = 1) :
    graphSymbol k q a = 0 := graphSymbol_steinberg k q a i j hij hab

open Lean in
run_cmd do
  for name in #[``coefficientMap_boundary, ``_root_.Motivic.DiagonalCoordinateInsertion.quotientMap,
      ``rawMap, ``rawMap_singularClass,
      ``factor_axis, ``varyingPair, ``rationalPair_varyingPair, ``varyingPair_axis,
      ``pairInsertion, ``pairInsertion_quotient, ``rawMap_pairSymbol, ``graphSymbol_steinberg,
      ``actual_insertion_boundary, ``actual_steinberg] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual fixed-coordinate insertion and Steinberg use only standard foundations."

end MotivicTest.DiagonalCoordinateInsertion
