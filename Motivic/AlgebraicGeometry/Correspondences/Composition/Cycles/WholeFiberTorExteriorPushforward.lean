/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.Restriction.Open
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.WholeFiberTorExteriorDecomposition
public import Motivic.AlgebraicGeometry.Correspondences.Exterior.Image.Generic

/-!
# Attach the whole-open Tor cycle to actual exterior pushforward

The existing whole-open Tor cycle is the open restriction of the global
signed ORIGINAL component-exterior fundamental-cycle sum. This follows from
the proved actual generic partition, full closed-fiber multiplicities, and
finite-pushforward/open-restriction compatibility; no cycle identity is supplied
as a hypothesis.

Its actual finite map restricted to the affine target open then pushes this
cycle to the restriction of the global exterior pushforward. The companion
consumer substitutes the proved global original-degree image-exterior formula.
This is the left affine-open attachment targeted in plan §6A. The remaining
diagonal realization, iterated incidence pairing, and associativity are outside
this result. The original whole opens may be singular or nonreduced.

SOURCE-ONLY PROPOSAL: this module, its consumer, and transitive exterior
residue-tensor/branch/degree/decomposition prerequisites are not claimed accepted.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

universe u

namespace AlgebraicGeometry.Scheme.Cycles.BaseChange.ComponentDecomposition

variable {P S T : Scheme.{u}} (p : P ⟶ S) (t : T ⟶ S) [Flat t]
  [IsNoetherian P] [IsNoetherian (pullback p t : Scheme.{u})]
  (U : (pullback p t : Scheme.{u}).Opens) [IsNoetherian U.toScheme]

local instance originalComponentExteriorNoetherian (z : genericPoints P) :
    IsNoetherian (componentExterior p t z) :=
  isNoetherian_of_finiteType (componentExteriorInclusion p t z)

/-- The full local closed-fiber cycle is the open restriction of the global
original-component sum. Every original signed coefficient is retained. -/
theorem ofGenericCoefficients_eq_openRestriction_component_sum (c : genericPoints P → ℤ) :
    letI := IntegralCycle.genericPointFintype P
    IntegralCycle.ofGenericCoefficients U.toScheme
        (fun w => c (componentGeneric p t U w) * closedFiberMultiplicity p t U w) =
      IntegralCycle.openRestriction U
        (∑ z : genericPoints P, c z •
          IntegralCycle.finitePushforward (componentExteriorInclusion p t z)
            (fundamentalCycle (componentExterior p t z))) := by
  classical
  let := IntegralCycle.genericPointFintype P
  rw [ofGenericCoefficients_eq_component_sum, map_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [map_zsmul, IntegralCycle.openRestriction_finitePushforward_fundamentalCycle]

end AlgebraicGeometry.Scheme.Cycles.BaseChange.ComponentDecomposition

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme

open _root_.AlgebraicGeometry.Scheme.Cycles.BaseChange.ComponentDecomposition

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

local instance wholeExteriorPushforward_factorFlat : Flat (H.projection ≫ Z.hom) := by
  let : Subsingleton (Spec (.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  let : IsIntegral (Spec (.of k)) := inferInstance
  exact Flat.instOfSubsingletonCarrierCarrierCommRingCatOfIsIntegral
    (Y := Spec (.of k)) (H.projection ≫ Z.hom)

local instance wholeExteriorPushforward_sourceNoetherian :
    IsNoetherian (F.leftIntermediateSupportProduct G H) :=
  isNoetherian_of_finiteType
    (pullback.fst (F.incidenceTarget G ≫ Z.hom) (H.projection ≫ Z.hom))

local instance wholeExteriorPushforward_componentNoetherian
    (z : genericPoints (F.incidence G)) :
    IsNoetherian (componentExterior (F.incidenceTarget G ≫ Z.hom)
      (H.projection ≫ Z.hom) z) :=
  isNoetherian_of_finiteType
    (componentExteriorInclusion (F.incidenceTarget G ≫ Z.hom) (H.projection ≫ Z.hom) z)

open Classical in
/-- The original global component-exterior sum with actual signed pair Tor weights.
This is a definition, not a replacement for the existing whole-open Tor cycle. -/
def firstStageOriginalExteriorCycle : IntegralCycle (F.leftIntermediateSupportProduct G H) :=
  letI := IntegralCycle.genericPointFintype (F.incidence G)
  ∑ z : genericPoints (F.incidence G),
    F.incidenceTorCoefficient (S := Spec (.of k)) G z •
      IntegralCycle.finitePushforward
        (componentExteriorInclusion (F.incidenceTarget G ≫ Z.hom) (H.projection ≫ Z.hom) z)
        (fundamentalCycle
          (componentExterior (F.incidenceTarget G ≫ Z.hom) (H.projection ≫ Z.hom) z))

variable (V : (F.leftIntermediateImageProduct G H).affineOpens)

/-- The EXISTING whole-open Tor cycle is the restriction of the actual original
signed component-exterior cycle. No unknown cycle equality is a premise. -/
theorem firstStageWholeTorGenericCycle_eq_openRestriction_originalExteriorCycle :
    F.firstStageWholeTorGenericCycle G H V =
      IntegralCycle.openRestriction ((F.leftIntermediateImageMap G H) ⁻¹ᵁ V)
        (F.firstStageOriginalExteriorCycle G H) := by
  rw [F.firstStageWholeTorGenericCycle_eq_pair_mul G H V]
  exact ofGenericCoefficients_eq_openRestriction_component_sum _ _ _
    (F.incidenceTorCoefficient (S := Spec (.of k)) G)

/-- Actual finite pushforward on the affine open attaches the existing whole
Tor cycle to the global original exterior realization. -/
theorem firstStageWholeTorGenericCycle_finitePushforward_eq_openRestriction :
    IntegralCycle.finitePushforward (F.leftIntermediateImageMap G H ∣_ V)
        (F.firstStageWholeTorGenericCycle G H V) =
      IntegralCycle.openRestriction V
        (IntegralCycle.finitePushforward (F.leftIntermediateImageMap G H)
          (F.firstStageOriginalExteriorCycle G H)) := by
  rw [F.firstStageWholeTorGenericCycle_eq_openRestriction_originalExteriorCycle G H V,
    IntegralCycle.openRestriction_finitePushforward]

/-- This specific restricted finite map preserves actual component generics.
It uses the proved whole-map geometry and the actual open inclusions. -/
theorem firstStageWholeRestrictedMap_mem_genericPoints
    (w : genericPoints (F.firstStageWholeOpen G H V)) :
    (F.leftIntermediateImageMap G H ∣_ V) w.1 ∈ genericPoints V.1.toScheme := by
  apply mem_genericPoints_of_isOpenImmersion V.1.ι
  simpa only [Scheme.Opens.ι_apply, morphismRestrict_base_coe] using
    F.leftIntermediateImageMap_mem_genericPoints k G H w.1.1
      (F.firstStageWholeGenericOriginal G H V w).2

/-- All nongeneric coefficients of the actual pushed whole-open Tor cycle
vanish. Finiteness alone is never used to assert generic preservation. -/
theorem firstStageWholeTorGenericCycle_finitePushforward_offGeneric
    (y : V.1.toScheme) (hy : y ∉ genericPoints V.1.toScheme) :
    IntegralCycle.toPoints
      (IntegralCycle.finitePushforward (F.leftIntermediateImageMap G H ∣_ V)
        (F.firstStageWholeTorGenericCycle G H V)) y = 0 := by
  rw [firstStageWholeTorGenericCycle,
    IntegralCycle.toPoints_finitePushforward_ofGenericCoefficients_apply]
  exact IntegralCycle.genericPushforwardCoefficient_eq_zero_of_not_generic
    (F.leftIntermediateImageMap G H ∣_ V)
    (F.firstStageWholeRestrictedMap_mem_genericPoints G H V) _ y hy

end Motivic.FiniteCorrespondenceGenerator
