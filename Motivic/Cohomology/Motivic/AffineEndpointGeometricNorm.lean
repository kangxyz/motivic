/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.AffineEndpointResidueScalar

/-! # Full original geometric endpoint norms are the original valuation sums -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteFlatCurve AlgebraicGeometry.FiniteAffineEndpointBranches
open scoped Polynomial BigOperators
universe u
namespace Motivic.AffineEndpointGeometricNorm
open MilnorK AffineEndpointResidueScalar DiagonalResiduePointEvaluation
open MilnorK.AffineEndpointGeometry MilnorK.DedekindResidue
variable (k S : Type u) [Field k] [CharZero k] [CommRing S] [IsDedekindDomain S]
  [Algebra k[X] S] [Module.Finite k[X] S] [Module.IsTorsionFree k[X] S]
  [Algebra k S] [IsScalarTower k k[X] S]

attribute [local instance] Classical.decEq DedekindResidue.polynomialPointResidueCharZero
local instance baseFinite : IsFinite (baseMap (k := k) S) :=
  (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
local instance fiberFintype (a : k) : Fintype (fiber (baseMap S) a) := Fintype.ofFinite _

/-- The actual full endpoint fundamental coefficients multiply the actual residue norms. -/
def geometricEndpointValue (a : k) (n : ℕ) (u : Fin n → Sˣ) : K k n :=
  ∑ x : fiber (baseMap S) a,
    (IntegralCycle.toPoints (fundamentalCycle (fiber (baseMap S) a)) x) •
      residueValue (fiberBase k S a)
        (fun i => Units.map (restrictScalar k S a).toMonoidHom (u i)) x

omit [Algebra k S] [IsScalarTower k k[X] S] in
/-- Any actual finite torus map with these literal restricted units evaluates its
full fundamental pushforward to the original geometric endpoint norm. -/
theorem cycleValue_eq_geometricEndpointValue (a : k) (n : ℕ) (u : Fin n → Sˣ)
    (j : fiber (baseMap S) a ⟶ DiagonalFinitePointEvaluation.ambient k n) [IsFinite j]
    (hp : j ≫ pullback.fst (SmoothSite.base (Spec (.of k))).hom
      (SmoothSite.torusPower (.of k) n).hom = fiberBase k S a)
    (hu : ∀ i, DiagonalFiniteFundamentalEvaluation.schemeCoordinateUnit j i =
      Units.map (restrictScalar k S a).toMonoidHom (u i))
    (α : WeightOnePointNorm.point k ⟶ DiagonalCycleSymbols.target k n)
    (hα : FiniteCorrespondence.toIntegralCycle α =
      IntegralCycle.finitePushforward j (fundamentalCycle (fiber (baseMap S) a))) :
    DiagonalPointNorm.cycleValue k n α = geometricEndpointValue k S a n u := by
  have h := cycleValue_eq_residue_sum_of_finite (fiberBase k S a) j hp α hα
  simpa only [geometricEndpointValue, funext hu] using h

variable (E : Type u) [Field E] [Algebra S E] [IsFractionRing S E]
  [Algebra k[X] E] [IsScalarTower k[X] S E]
  [Algebra (RatFunc k) E] [IsScalarTower k[X] (RatFunc k) E]

/-- Full scheme multiplicities and all residue fields agree with the original
field's full valuation sum through the actual point bijection and scalar maps. -/
theorem geometricEndpointValue_eq (a : k) (n : ℕ) (u : Fin n → Sˣ) :
    geometricEndpointValue k S a n u = endpointWeightedResidueSum k S E a n u := by
  rw [endpointWeightedResidueSum_eq_baseNormSum]
  rw [← (originalBranchEquiv k S a).sum_comp]
  unfold geometricEndpointValue
  apply Finset.sum_congr rfl
  intro x _
  rw [fundamentalCoefficient_eq_originalOrder k S E,
    residueValue_original_units k S]
  rfl

variable [FiniteDimensional (RatFunc k) E]

include E in
/-- Every positive-weight tuple of actual global units has equal full geometric
endpoint evaluations; singular/nonreduced endpoint fibers are retained. -/
theorem geometricEndpointValue_eq_endpoint (a b : k) (n : ℕ)
    (u : Fin (n + 1) → Sˣ) :
    geometricEndpointValue k S a (n + 1) u = geometricEndpointValue k S b (n + 1) u := by
  rw [geometricEndpointValue_eq k S E, geometricEndpointValue_eq k S E]
  exact endpointWeightedResidueSum_eq k S E a b n u

end Motivic.AffineEndpointGeometricNorm
