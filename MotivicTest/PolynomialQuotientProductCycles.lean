/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.PolynomialQuotient.Product
public import Lean

/-! # Whole quotient cycle additivity, including a repeated zero root -/
public noncomputable section
open CategoryTheory AlgebraicGeometry Polynomial
open AlgebraicGeometry.PolynomialOpenQuotient
universe u
namespace MotivicTest.PolynomialQuotientProductCycles

/-- Arbitrary monic factors, with no coprimality or unit constant term hypothesis. -/
theorem actual_product_cycle
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (p q : R[X]) (hp : p.Monic) (hq : q.Monic) :
    quotientCycle (p * q) (hp.mul hq) = quotientCycle p hp + quotientCycle q hq :=
  quotientCycle_mul p q hp hq

/-- The doubled zero root retains both copies of its actual generic local length. -/
theorem doubled_zero_root (k : Type u) [Field k] :
    quotientCycle ((X : k[X]) * X) (monic_X.mul monic_X) =
      quotientCycle (X : k[X]) monic_X + quotientCycle (X : k[X]) monic_X :=
  quotientCycle_mul X X monic_X monic_X

/-- The cycle wrapper is the actual finite pushforward, not a newly axiomatized cycle. -/
theorem actual_cycle_definition (R : Type u) [CommRing R] [IsNoetherianRing R]
    (p : R[X]) (hp : p.Monic) :
    letI : IsFinite (source p) := source_finite p hp
    letI : IsNoetherian (Spec (.of (AdjoinRoot p))) :=
      Scheme.isNoetherian_of_finiteType (source p)
    quotientCycle p hp = Scheme.IntegralCycle.finitePushforward (inclusion p)
      (Scheme.fundamentalCycle (Spec (.of (AdjoinRoot p)))) := rfl

open Lean in
run_cmd do
  for name in #[``actual_product_cycle, ``doubled_zero_root, ``actual_cycle_definition,
      ``inclusion_kernel_stalk, ``polynomialGerm_regular, ``quotientCycle_mul] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Whole polynomial quotient cycles and repeated factors: standard foundations only."

end MotivicTest.PolynomialQuotientProductCycles
