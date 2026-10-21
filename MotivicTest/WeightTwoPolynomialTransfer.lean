/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightTwo.PolynomialTransfer
public import Lean.Util.CollectAxioms

/-!
# Consumers of the whole polynomial finite-transfer decomposition

The statements retain the actual maximal quotient fields, their original
scalar maps and localized lengths. No irreducibility, reducedness, or
separability assumption is introduced by these consumers.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial Motivic
open Polynomial.TwoUnitPolynomialFamily
open _root_.AlgebraicGeometry.Scheme.FiniteAlgebra
open _root_.Motivic.WeightOneFundamentalNorm
open WeightTwoCubicBoundary
open WeightTwoCorestriction
open WeightTwoPolynomialTransfer
open scoped BigOperators

universe u

namespace MotivicTest.WeightTwoPolynomialTransfer

variable {k : Type u} [Field k]

/-- The canonical field structure on a maximal quotient used by these consumers. -/
local instance quotientField {R : Type u} [CommRing R] (q : MaximalSpectrum R) :
    Field (R ⧸ q.asIdeal) := Ideal.Quotient.field q.asIdeal

/-- The affine equality uses the literal quotient images of both original units. -/
theorem actual_affine_branch (p : k[X])
    (h0 : IsUnit (p.eval 0)) (h1 : IsUnit (p.eval 1))
    (q : MaximalSpectrum (AdjoinRoot p)) :
    quotientMap q ≫ polynomialInclusion p h0 h1 =
      scalarPoint (k := k) (WeightTwoSymbols.rationalPair (AdjoinRoot p ⧸ q.asIdeal)
        (Units.map (Ideal.Quotient.mk q.asIdeal).toMonoidHom (rootUnit p h0))
        (Units.map (Ideal.Quotient.mk q.asIdeal).toMonoidHom (oneSubRootUnit p h1))) :=
  polynomialQuotient_scalarPoint p h0 h1 q

/-- The actual polynomial correspondence is the complete local-length-weighted transfer. -/
theorem actual_polynomial_transfer (p : k[X]) (hp : p.Monic)
    (h0 : IsUnit (p.eval 0)) (h1 : IsUnit (p.eval 1)) :
    letI := hp.finite_adjoinRoot
    letI : IsArtinianRing (AdjoinRoot p) := .of_finite k _
    letI : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
    polynomialCycle p hp h0 h1 = ∑ q : MaximalSpectrum (AdjoinRoot p),
      ((Module.length (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal)).toNat : ℤ) •
        pointPushforward (k := k) ((Cor.graphFunctor (AdjoinRoot p ⧸ q.asIdeal)).map
          (WeightTwoSymbols.rationalPair (AdjoinRoot p ⧸ q.asIdeal)
            (residueRootUnit p h0 q) (residueComplementUnit p h1 q))) :=
  polynomialCycle_eq_sum_pointPushforward p hp h0 h1

/-- The original H22 cycle class uses genuine finite corestriction from every quotient field. -/
theorem actual_homology_transfer (p : k[X]) (hp : p.Monic)
    (h0 : IsUnit (p.eval 0)) (h1 : IsUnit (p.eval 1)) :
    letI := hp.finite_adjoinRoot
    letI : IsArtinianRing (AdjoinRoot p) := .of_finite k _
    letI : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
    WeightTwoSymbols.cycleClass k (polynomialCycle p hp h0 h1) =
      ∑ q : MaximalSpectrum (AdjoinRoot p),
        ((Module.length (Localization.AtPrime q.asIdeal)
          (Localization.AtPrime q.asIdeal)).toNat : ℤ) •
          corestriction (k := k) (WeightTwoSymbols.graphSymbol (AdjoinRoot p ⧸ q.asIdeal)
            (residueRootUnit p h0 q) (residueComplementUnit p h1 q)) :=
  cycleClass_polynomialCycle_eq_sum_corestriction p hp h0 h1

/-- The matching full complement norm is exactly evaluation of the original polynomial. -/
theorem actual_complement_norm (p : k[X]) (hp : p.Monic)
    (h1 : IsUnit (p.eval 1)) :
    letI := hp.finite_adjoinRoot
    letI : IsArtinianRing (AdjoinRoot p) := .of_finite k _
    letI : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
    (∏ q : MaximalSpectrum (AdjoinRoot p),
      Algebra.norm k (residueComplementUnit p h1 q : AdjoinRoot p ⧸ q.asIdeal) ^
        (Module.length (Localization.AtPrime q.asIdeal)
          (Localization.AtPrime q.asIdeal)).toNat) = p.eval 1 :=
  prod_residueComplement_norm_eq_eval_one p hp h1

open Lean in
run_cmd do
  for name in #[``residueComplementUnit_val, ``rationalPair_torusMap,
      ``polynomialQuotient_scalarPoint,
      ``finitePushforward_quotientMap, ``polynomialQuotient_pushforward,
      ``polynomialCycle_eq_sum_pointPushforward,
      ``cycleClass_polynomialCycle_eq_sum_corestriction,
      ``prod_residueComplement_norm_eq_eval_one, ``actual_affine_branch,
      ``actual_polynomial_transfer, ``actual_homology_transfer, ``actual_complement_norm] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Whole polynomial transfers use only standard foundations."

end MotivicTest.WeightTwoPolynomialTransfer
