/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.AlgebraicGeometry.Correspondences.Moving.Polynomial.Open.LinearGraph
public import Lean
/-! # Actual linear quotient graphs, including the nonunit zero coordinate -/
public noncomputable section
open CategoryTheory AlgebraicGeometry Polynomial
open Motivic Motivic.PolynomialOpenSpans
universe u
namespace MotivicTest.PolynomialOpenLinearGraph

/-- The affine coordinate zero needs no unit hypothesis. -/
theorem actual_zero_graph (k : Type u) [Field k] :
    affineCycle (k := k) (X - C (0 : k)) (monic_X_sub_C 0) =
      (Cor.graphFunctor k).map (coordinateMorphism (k := k) (0 : k)) :=
  affineCycle_linear_graph 0

/-- An arbitrary actual lift to the original principal open retains its graph. -/
theorem actual_open_graph (k R : Type u) [Field k] [CommRing R]
    [Algebra k R] [Algebra.Smooth k R] (a : R) (f : k[X])
    (hf : IsUnit (AdjoinRoot.mk (X - C a) (f.map (algebraMap k R))))
    (j : affineSite (k := k) (R := R) ⟶ openSite f)
    (hj : j ≫ openInclusion f = coordinateMorphism a) :
    cycle (X - C a) (monic_X_sub_C a) f hf = (Cor.graphFunctor k).map j :=
  cycle_linear_graph a f hf j hj

open Lean in
run_cmd do
  for name in #[``actual_zero_graph, ``actual_open_graph,
      ``affineCycle_linear_graph, ``cycle_linear_graph] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual linear quotient graph identities: standard foundations only."

end MotivicTest.PolynomialOpenLinearGraph
