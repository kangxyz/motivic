/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.AffineTorusDivisorNaturality
public import Lean.Util.CollectAxioms

/-! # Direct audit of actual ordinary affine divisor naturality -/

@[expose] public noncomputable section

open Motivic Motivic.AffineTorusPolynomialPresentation Polynomial.BoundaryOneRationalFunctions
open Polynomial AlgebraicGeometry AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

namespace MotivicTest.AffineTorusDivisorNaturality

variable {k R S : Type u} [Field k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S] [Algebra.Smooth k R] [Algebra.Smooth k S]
  [IsDomain R] [IsDomain S] [IsNoetherianRing R] [IsNoetherianRing S]

theorem actual_graph_divisor_natural (φ : R →ₐ[k] S) (f : Additive (group R)) :
    affineRestriction φ (boundaryDivisor f) =
      boundaryDivisor ((Polynomial.BoundaryOneRationalFunctions.map φ.toRingHom).toAdditive f) :=
  boundaryDivisor_natural φ f

open Lean in
run_cmd do
  for name in #[``AdjoinRootBaseChange.square, ``AdjoinRootBaseChange.isPushout,
      ``AdjoinRootBaseChange.isPullback, ``polynomialBaseChangeMap, ``polynomial_isPullback,
      ``polynomialConstant_map_unit, ``polynomialBaseChangeMap_laurent,
      ``ambientIso_hom_snd, ``polynomialBaseChangeMap_target, ``baseMap_smooth,
      ``baseMap_separated, ``baseMap_quasiCompact, ``affineSite, ``affineMorphism,
      ``generator_projection_flat, ``supportBaseChange_isPullback, ``supportBaseChangeIso,
      ``supportBaseChangeIso_fst, ``supportBaseChangeIso_snd, ``supportBaseChangeIso_inclusion,
      ``graph_generator_eq_polynomialCycle, ``affineRestriction, ``affineRestriction_generator,
      ``cycleRationalFunction_affineRestriction_generator, ``cycleRationalFunction_natural,
      ``rationalDivisorHom_natural, ``boundaryDivisor_natural, ``polynomialCycle_natural,
      ``actual_graph_divisor_natural] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual graph divisor naturality uses only standard Lean foundations."

end MotivicTest.AffineTorusDivisorNaturality
