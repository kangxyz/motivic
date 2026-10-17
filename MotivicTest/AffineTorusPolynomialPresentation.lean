/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.AffineTorusPolynomialPresentation
public import Lean.Util.CollectAxioms

/-! # Direct consumers for original integral finite torus support algebras -/

@[expose] public noncomputable section

open Polynomial Motivic.AffineTorusPolynomialPresentation

universe u

namespace MotivicTest.AffineTorusPolynomialPresentation

variable {k R : Type u} [Field k] [CommRing R] [IsDomain R]
  [Algebra k R] [Algebra.Smooth k R] (Z : Generator k R)

def actual_support_presentation :
    AdjoinRoot (minpoly R (coordinateUnit Z : coordinateRing Z)) ≃ₐ[R] coordinateRing Z :=
  polynomialEquiv Z

theorem actual_support_coordinate :
    actual_support_presentation Z
      (AdjoinRoot.root (minpoly R (coordinateUnit Z : coordinateRing Z))) =
        (coordinateUnit Z : coordinateRing Z) := polynomialEquiv_root Z

theorem actual_support_finite_free :
    Module.Finite R (coordinateRing Z) ∧ Module.Free R (coordinateRing Z) :=
  ⟨inferInstance, coordinateFree Z⟩

open Lean in
run_cmd do
  for name in #[``baseMap, ``Generator, ``ambient_isPullback, ``ambientIso,
      ``ambientIso_hom_fst, ``supportAffine, ``coordinateDomain, ``scalarMap,
      ``coordinateAlgebra, ``coordinateFinite, ``laurentEmbedding,
      ``laurentEmbedding_closed, ``laurentEmbedding_projection, ``laurentPullback,
      ``coordinateUnit, ``laurentPullback_C, ``laurent_eval_surjective,
      ``scalarMap_injective, ``coordinateTorsionFree, ``polynomialEquiv,
      ``polynomialEquiv_root, ``coordinatePolynomial_constant_isUnit, ``coordinateFree,
      ``actual_support_presentation, ``actual_support_coordinate, ``actual_support_finite_free] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original affine torus support presentations use only standard Lean foundations."

end MotivicTest.AffineTorusPolynomialPresentation
