/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Dedekind.AffineEndpointNormEquality
public import Motivic.Aglib.AlgebraicGeometry.Cycles.FiniteCurve.BranchOrders

/-! # Actual normalization of an arbitrary integral finite affine curve support -/

@[expose] public noncomputable section
namespace AlgebraicGeometry.FiniteCurveNormalization
open _root_.AlgebraicGeometry.Scheme.Normalization.FiniteCurve

open Polynomial MilnorK MilnorK.DedekindResidue

universe u
variable (k B : Type u) [Field k] [CharZero k] [CommRing B] [IsDomain B]
  [Algebra k[X] B] [Module.Finite k[X] B] [FaithfulSMul k[X] B]

omit [CharZero k] [IsDomain B] [Module.Finite k[X] B] in
/-- The original polynomial scalar map into the original fraction field is injective. -/
theorem fractionScalar_injective :
    Function.Injective (algebraMap k[X] (FractionRing B)) := by
  rw [IsScalarTower.algebraMap_eq k[X] B (FractionRing B)]
  exact (IsFractionRing.injective B (FractionRing B)).comp
    (FaithfulSMul.algebraMap_injective k[X] B)

/-- The actual rational parameter action on the original fraction field. -/
@[instance_reducible]
def rationalAlgebra : Algebra (RatFunc k) (FractionRing B) :=
  (IsFractionRing.lift (K := RatFunc k) (fractionScalar_injective k B)).toAlgebra

attribute [local instance] rationalAlgebra

/-- The chosen rational action extends the unchanged polynomial parameter. -/
instance rationalTower : IsScalarTower k[X] (RatFunc k) (FractionRing B) := by
  apply IsScalarTower.of_algebraMap_eq
  intro a
  exact (IsFractionRing.lift_algebraMap (K := RatFunc k)
    (fractionScalar_injective k B) a).symm

/-- The actual rational-function extension is finite, not an extra curve assumption. -/
instance rationalFinite : FiniteDimensional (RatFunc k) (FractionRing B) :=
  Module.Finite.of_isLocalization k[X] B (nonZeroDivisors k[X])

omit [CharZero k] [Module.Finite k[X] B] in
/-- Normalization retains torsion-freeness for the original parameter map. -/
theorem normalizationTorsionFree : Module.IsTorsionFree k[X] (ring B) := by
  let := ring_faithfulSMul_base (k := k) B
  exact Module.isTorsionFree_iff_algebraMap_injective.mpr
    (FaithfulSMul.algebraMap_injective k[X] (ring B))

/-- The two endpoint sums for the actual normalization of every original finite
integral affine curve agree. Its fraction field and all global units are unchanged. -/
theorem normalized_endpoint_sum_eq (a b : k) (n : ℕ) (u : Fin (n + 1) → Bˣ) :
    letI := ring_isDedekindDomain (k := k) B
    letI := ring_finite_base (k := k) B
    letI := normalizationTorsionFree k B
    endpointWeightedResidueSum k (ring B) (FractionRing B) a (n + 1)
      (Units.map (algebraMap B (ring B)).toMonoidHom ∘ u) =
    endpointWeightedResidueSum k (ring B) (FractionRing B) b (n + 1)
      (Units.map (algebraMap B (ring B)).toMonoidHom ∘ u) := by
  let := ring_isDedekindDomain (k := k) B
  let := ring_finite_base (k := k) B
  let := normalizationTorsionFree k B
  exact endpointWeightedResidueSum_eq k (ring B) (FractionRing B) a b n _

end AlgebraicGeometry.FiniteCurveNormalization
