/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Diagonal.PointNorm
public import Lean.Util.CollectAxioms

/-! Consumers of literal all-weight finite-point Milnor evaluation. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Motivic
open Motivic.DiagonalCycleSymbols Motivic.DiagonalPointNorm MilnorK

universe u

namespace MotivicTest.DiagonalPointNorm

variable (k : Type u) [Field k] [CharZero k]

/-- Every position of every rational tuple is evaluated in the original Milnor group. -/
theorem actual_rational_tuple (q : ℕ) (a : Fin q → kˣ) :
    cycleValue k q ((Cor.graphFunctor k).map (rationalTuple k q a)) = symbol a :=
  cycleValue_rationalTuple a

/-- Negative coefficients are genuine signed cycle multiplicities. -/
theorem actual_signed_rational_tuple (q : ℕ) (a : Fin q → kˣ) (m : ℤ) :
    cycleValue k q (m • (Cor.graphFunctor k).map (rationalTuple k q a)) = m • symbol a := by
  exact (map_zsmul (cycleValue k q) m
    (show WeightOnePointNorm.point k ⟶ target k q from
      (Cor.graphFunctor k).map (rationalTuple k q a))).trans
        (congrArg (m • ·) (cycleValue_rationalTuple a))

/-- Higher-weight supports use their entire actual finite coordinate field. -/
theorem actual_whole_support (q : ℕ) (Z : Generator k q) :
    cycleValue k q Z.cycle =
      finiteExtensionNorm k (coordinateRing Z) q (symbol (coordinateUnit Z)) :=
  cycleValue_cycle Z

/-- No positive-weight hypothesis is silently introduced. -/
theorem actual_empty_tuple (a : Fin 0 → kˣ) :
    cycleValue k 0 ((Cor.graphFunctor k).map (rationalTuple k 0 a)) = symbol a :=
  cycleValue_rationalTuple a

/-- An arbitrary coordinate equal to one is killed already on raw cycles. -/
theorem actual_identity_coordinate (q : ℕ) (a : Fin q → kˣ) (i : Fin q) (hi : a i = 1) :
    cycleValue k q ((Cor.graphFunctor k).map (rationalTuple k q a)) = 0 :=
  cycleValue_rationalTuple_one a i hi

/-- Unrelated identity positions on different finite supports are allowed. -/
theorem actual_signed_identity_support (q : ℕ)
    (α : WeightOnePointNorm.point k ⟶ target k q)
    (hα : ∀ Z ∈ α.support, ∃ i : Fin q, coordinateUnit Z i = 1) :
    cycleValue k q α = 0 := cycleValue_eq_zero_of_identity_support α hα

open Lean in
run_cmd do
  for name in #[``Generator, ``coordinateRing, ``supportIsoSpec, ``scalarMap,
      ``coordinateFinite, ``coordinateRing_isField, ``coordinateUnit, ``generatorValue,
      ``cycleValue, ``cycleValue_single, ``cycleValue_cycle,
      ``generatorValue_eq_zero_of_coordinate_one, ``cycleValue_eq_zero_of_identity_support,
      ``graph_finrank, ``graph_coordinate, ``generatorValue_graph, ``cycleValue_graph,
      ``rationalCoordinate_rationalTuple, ``cycleValue_rationalTuple,
      ``cycleValue_rationalTuple_one, ``actual_rational_tuple, ``actual_signed_rational_tuple,
      ``actual_whole_support, ``actual_empty_tuple, ``actual_identity_coordinate,
      ``actual_signed_identity_support] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual all-weight point evaluation uses only standard foundations."

end MotivicTest.DiagonalPointNorm
