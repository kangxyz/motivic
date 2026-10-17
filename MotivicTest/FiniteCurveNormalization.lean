/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.FiniteCurveNormalization

/-!
# Consumers of normalization over the unchanged finite curve base

The only curve input is a finite faithful domain algebra over the original
`k[X]`. Normality, finite normalization, and a finite fraction-field extension
are conclusions, not supplied premises. Endpoint tests use all original
Cartier multiplicities and allow arbitrary signed cycle coefficients.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Motivic
open AlgebraicGeometry.FiniteFlatCurve Motivic.FiniteCurveNormalization
open scoped Polynomial

universe u

namespace MotivicTest.FiniteCurveNormalization

variable {k : Type u} [Field k] [CharZero k]
  (B : Type u) [CommRing B] [IsDomain B]
  [Algebra k[X] B] [Module.Finite k[X] B] [FaithfulSMul k[X] B]

attribute [local instance] FractionRing.liftAlgebra

/-- Generic finiteness is derived from the actual original finite algebra. -/
example : Module.Finite (FractionRing k[X]) (FractionRing B) := fractionRing_finite B

/-- The original characteristic-zero field provides separability. -/
example : Algebra.IsSeparable (FractionRing k[X]) (FractionRing B) := fractionRing_separable B

/-- The normalization is finite over the original parameter ring. -/
example : Module.Finite k[X] (ring B) := ring_finite_base B

include k in
/-- Finiteness over the singular curve is a proved conclusion. -/
example : Module.Finite B (ring B) := ring_finite (k := k) B

include k in
/-- Normality and dimension at most one come from the actual closure. -/
example : IsDedekindDomain (ring B) := ring_isDedekindDomain (k := k) B

include k in
/-- The degree-one assertion uses the actual generic residue map. -/
theorem genericDegreeOne :
    (normalizationMap B).residueDegree (genericPoint (Spec (.of (ring B)))) = 1 := by
  let : Module.Finite B (ring B) := ring_finite (k := k) B
  exact normalizationMap_residueDegree B

omit [CharZero k] [Module.Finite k[X] B] [FaithfulSMul k[X] B] in
/-- The scalar t-a is unchanged by the original normalization inclusion. -/
theorem originalEndpointScalar (a : k) :
    algebraMap B (ring B) (algebraMap k[X] B (Polynomial.X - Polynomial.C a)) =
      algebraMap k[X] (ring B) (Polynomial.X - Polynomial.C a) :=
  (IsScalarTower.algebraMap_apply k[X] B (ring B) _).symm

/-- No normality, flatness, branch choice, or reduced endpoint premise is supplied. -/
theorem wholeEndpoint (a : k) :
    letI : IsFinite (normalizationMap B) := normalizationMap_isFinite (k := k) B
    letI : IsNoetherian (Spec (.of B)) := isNoetherian_of_finiteType (baseMap (k := k) B)
    letI : IsNoetherian (Spec (.of (ring B))) :=
      isNoetherian_of_finiteType (normalizationMap B)
    IntegralCycle.finitePushforward (fiberMap (baseMap (k := k) B) a (normalizationMap B))
        (fundamentalCycle (fiber (normalizationMap B ≫ baseMap (k := k) B) a)) =
      fundamentalCycle (fiber (baseMap (k := k) B) a) :=
  finitePushforward_fiber B a

/-- Every target point retains the sum of all normalized branch lengths,
with the original residue weights. The target length is not reduced to one. -/
theorem wholeEndpointLengths (a : k) (y : fiber (baseMap (k := k) B) a) :
    (∑ᶠ x : {x : Spec (.of (ring B)) //
        normalizationMap B x = fiberInclusion (baseMap (k := k) B) a y},
      ((normalizationMap B).residueDegree x.1 : ℤ) *
        ((Module.length ((Spec (.of (ring B))).presheaf.stalk x.1)
          (((Spec (.of (ring B))).presheaf.stalk x.1) ⧸
            Ideal.ofList [scalar (normalizationMap B ≫ baseMap (k := k) B) a x.1])).toNat : ℤ)) =
      ((Module.length ((Spec (.of B)).presheaf.stalk
        (fiberInclusion (baseMap (k := k) B) a y))
        (((Spec (.of B)).presheaf.stalk (fiberInclusion (baseMap (k := k) B) a y)) ⧸
          Ideal.ofList [scalar (baseMap (k := k) B) a
            (fiberInclusion (baseMap (k := k) B) a y)])).toNat : ℤ) := by
  let : IsFinite (normalizationMap B) := normalizationMap_isFinite (k := k) B
  let : IsNoetherian (Spec (.of B)) := isNoetherian_of_finiteType (baseMap (k := k) B)
  let : IsNoetherian (Spec (.of (ring B))) :=
    isNoetherian_of_finiteType (normalizationMap B)
  have h := congrArg (fun z => IntegralCycle.toPoints z y) (wholeEndpoint B a)
  simpa only [fiberMap_fundamentalCoefficient, fiber_fundamentalCoefficient] using h

/-- Both endpoint signs, and any further genuine finite pushforward, are retained. -/
theorem signedEndpoint (a : k) {Q : Scheme.{u}}
    (g : fiber (baseMap (k := k) B) a ⟶ Q) [IsFinite g] (n : ℤ) :
    letI : IsFinite (normalizationMap B) := normalizationMap_isFinite (k := k) B
    letI : IsNoetherian (Spec (.of B)) := isNoetherian_of_finiteType (baseMap (k := k) B)
    letI : IsNoetherian (Spec (.of (ring B))) :=
      isNoetherian_of_finiteType (normalizationMap B)
    IntegralCycle.finitePushforward (fiberMap (baseMap (k := k) B) a (normalizationMap B) ≫ g)
        (n • fundamentalCycle (fiber (normalizationMap B ≫ baseMap (k := k) B) a)) =
      n • IntegralCycle.finitePushforward g (fundamentalCycle (fiber (baseMap (k := k) B) a)) := by
  let : IsFinite (normalizationMap B) := normalizationMap_isFinite (k := k) B
  let : IsNoetherian (Spec (.of B)) := isNoetherian_of_finiteType (baseMap (k := k) B)
  let : IsNoetherian (Spec (.of (ring B))) :=
    isNoetherian_of_finiteType (normalizationMap B)
  rw [IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply,
    map_zsmul, wholeEndpoint, map_zsmul]

/-- The identity finite curve is admitted without a separate normalization package. -/
example : IsFinite (normalizationMap k[X]) := normalizationMap_isFinite (k := k) k[X]

open Lean in
run_cmd do
  for name in #[
      ``ring_isFractionRing, ``ring_isIntegrallyClosed, ``ring_finrank,
      ``ring_algebraMap_injective, ``normalizationMap_surjective,
      ``normalizationMap_residueDegree, ``fractionRing_finite, ``fractionRing_separable,
      ``ring_isIntegralClosure_base, ``ring_finite_base, ``ring_isDedekindDomain,
      ``ring_finite, ``baseMap_isFinite, ``baseMap_surjective,
      ``normalizationMap_isFinite, ``normalizationMap_baseMap,
      ``finitePushforward_fiber, ``genericDegreeOne, ``originalEndpointScalar,
      ``wholeEndpoint, ``wholeEndpointLengths, ``signedEndpoint] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual finite curve normalization and endpoint cycles use only standard foundations."

end MotivicTest.FiniteCurveNormalization
