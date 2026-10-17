/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.QuadraticInfinitySchemeEmpty
/-! The whole same-family infinity scheme is empty, without reducing its equations. -/
set_option linter.hashCommand false
public noncomputable section
open AlgebraicGeometry
universe u
namespace QuadraticIncidence.InfinityChart
variable (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R]
  {σ : Type u} [Finite σ] (g : σ → R) (d : ℕ)
  (j : Exponent σ) (hj : monomialFunction k R g j ≠ 0)
  (c : Fin (d + 1) × Exponent σ → k)
  (hc : NoCommonInfinityZero k R g d c)

example : Ideal.span (Set.range (chartRow k R g d j c)) ⊔
    Ideal.span {infinityCoordinate k R g j} = ⊤ :=
  chartRow_infinity_span_eq_top k R g d j hj c hc

example : IsEmpty (Spec (.of (chart k R g j ⧸
    (Ideal.span (Set.range (chartRow k R g d j c)) ⊔
      Ideal.span {infinityCoordinate k R g j}))) : Scheme.{u}) :=
  isEmpty_chart_infinity_commonZero k R g d j hj c hc

#print axioms chartRow_infinity_span_eq_top
#print axioms nativeChartMapToRatioRing_row
#print axioms isEmpty_chart_infinity_commonZero
end QuadraticIncidence.InfinityChart
