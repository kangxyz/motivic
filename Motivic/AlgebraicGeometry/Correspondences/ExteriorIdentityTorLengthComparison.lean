/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.ExteriorIdentityIncidenceTorReduction
public import Motivic.AlgebraicGeometry.Correspondences.IncidenceMiddleKoszulLength

/-!
# Actual exterior incidence Tor lengths

The actual exterior incidence Tor lengths equal the original incidence Tor
lengths times the actual local closed-fiber length. The comparison uses the
same original middle equations on both sides and eliminates only the regular
parameter block. All higher Tor and all nilpotent closed-fiber structure remain.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingTheory.Sequence

universe u

namespace Motivic.FiniteCorrespondenceGenerator

variable {k : Type u} [Field k] {X Y Z : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom]

/-- The middle point is the original incidence's middle point after projection. -/
theorem exteriorIncidenceOldMiddlePoint_eq
    (w : (A.exteriorIdentityGenerator T).incidence (B.exteriorIdentityGenerator T)) :
    A.exteriorIncidenceOldMiddlePoint B T w =
      correspondenceTripleMiddle X.hom Y.hom Z.hom
        (A.incidenceInclusion B (A.exteriorIncidenceOriginalCoordinate B T w)) :=
  (congrArg (fun f => f w) (A.exteriorIncidenceOriginalCoordinate_middle B T)).symm

omit [GeometricallyIntegral T.hom] in
private theorem originalTor_length_at_middle (v : A.incidence B) (y : Y.left)
    (hy : y = correspondenceTripleMiddle X.hom Y.hom Z.hom (A.incidenceInclusion B v))
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk (pullback.diagonal Y.hom y)))
    (hs : IsRegular ((pullback Y.hom Y.hom).presheaf.stalk (pullback.diagonal Y.hom y)) s)
    (hker : RingHom.ker ((pullback.diagonal Y.hom).stalkMap y).hom = Ideal.ofList s) (n : ℕ) :
    Module.length (A.incidenceAmbientStalk B v) (A.incidenceTor B v n) =
      Module.length ((A.supportProduct B).presheaf.stalk (A.incidenceToSupportProduct B v))
        ((Koszul.coefficientComplex
          (ModuleCat.of ((A.supportProduct B).presheaf.stalk (A.incidenceToSupportProduct B v))
            ((A.supportProduct B).presheaf.stalk (A.incidenceToSupportProduct B v)))
          (s.map (StalkTransport.pointedMap (A.originalCoefficientMiddlePair B)
            (A.incidenceToSupportProduct B v) (pullback.diagonal Y.hom y)
            ((congrArg (pullback.diagonal Y.hom) hy).trans
              (congrArg (fun f => f v)
                (A.originalIncidence_middle_isPullback B).w))).hom)).homology n) := by
  subst y
  exact A.incidenceTor_length_eq_middleKoszul B v s hs hker n

/-- The original coefficient scalar map at the actual projected incidence point. -/
abbrev exteriorIncidenceOriginalMiddleStalkMap
    (w : (A.exteriorIdentityGenerator T).incidence (B.exteriorIdentityGenerator T)) :=
  StalkTransport.pointedMap (A.originalCoefficientMiddlePair B)
    (A.incidenceToSupportProduct B (A.exteriorIncidenceOriginalCoordinate B T w))
    (pullback.diagonal Y.hom (A.exteriorIncidenceOldMiddlePoint B T w))
    ((congrArg (pullback.diagonal Y.hom) (A.exteriorIncidenceOldMiddlePoint_eq B T w)).trans
      (congrArg (fun f => f (A.exteriorIncidenceOriginalCoordinate B T w))
        (A.originalIncidence_middle_isPullback B).w))

/-- The original and surviving equation lists agree under the actual flat coefficient map. -/
theorem exteriorIncidenceRemainingList_eq
    (w : (A.exteriorIdentityGenerator T).incidence (B.exteriorIdentityGenerator T))
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (pullback.diagonal Y.hom (A.exteriorIncidenceOldMiddlePoint B T w)))) :
    A.exteriorIncidenceRemainingList B T w s =
      (s.map (A.exteriorIncidenceOriginalMiddleStalkMap B T w).hom).map
        (Diagonal.baseChangeStalkMap (A.exteriorIncidenceProjection_isPullback B T) w).hom := by
  have hmaps :
      A.exteriorIncidenceOriginalMiddleStalkMap B T w ≫
        Diagonal.baseChangeStalkMap (A.exteriorIncidenceProjection_isPullback B T) w =
      Diagonal.baseChangeStalkMap (exteriorAmbientRemaining_isPullback X Y Z T)
          ((A.exteriorIdentityGenerator T).incidenceInclusion (B.exteriorIdentityGenerator T) w) ≫
        A.exteriorIncidenceRemainingCoefficientStalkMap B T w := by
    exact StalkTransport.pointedMap_square
      (A.exteriorCoefficientQuotientProjection B T) (A.originalCoefficientMiddlePair B)
      (A.exteriorCoefficientQuotientInclusion B T) (exteriorAmbientRemainingPair X Y Z T)
      (A.exteriorCoefficientQuotientInclusion_remainingPair B T).symm
      (A.exteriorIncidenceToCoefficientQuotient B T w)
      (A.incidenceToSupportProduct B (A.exteriorIncidenceOriginalCoordinate B T w))
      (exteriorAmbientRemainingInclusion X Y Z T
        ((A.exteriorIdentityGenerator T).incidenceInclusion (B.exteriorIdentityGenerator T) w))
      (pullback.diagonal Y.hom (A.exteriorIncidenceOldMiddlePoint B T w))
      (congrArg (fun f => f w) (A.exteriorIncidenceToCoefficientQuotient_projection B T)).symm
      (Intersection.point_eq _ _ _ _ (A.exteriorRemainingIncidence_isPullback B T) w)
      ((congrArg (pullback.diagonal Y.hom)
        (A.exteriorIncidenceOldMiddlePoint_eq B T w)).trans
        (congrArg (fun f => f (A.exteriorIncidenceOriginalCoordinate B T w))
          (A.originalIncidence_middle_isPullback B).w))
      (congrArg (fun f => f
        ((A.exteriorIdentityGenerator T).incidenceInclusion (B.exteriorIdentityGenerator T) w))
        (exteriorAmbientRemaining_isPullback X Y Z T).w)
  simp only [exteriorIncidenceRemainingList, List.map_map]
  congr 1
  funext r
  exact (ConcreteCategory.congr_hom hmaps r).symm

/-- Every actual Tor degree retains the full local closed-fiber multiplier. -/
theorem exteriorIncidenceTor_length
    (w : (A.exteriorIdentityGenerator T).incidence (B.exteriorIdentityGenerator T)) (n : ℕ) :
    Module.length
      ((A.exteriorIdentityGenerator T).incidenceAmbientStalk (B.exteriorIdentityGenerator T) w)
      ((A.exteriorIdentityGenerator T).incidenceTor (B.exteriorIdentityGenerator T) w n) =
      Module.length (A.incidenceAmbientStalk B (A.exteriorIncidenceOriginalCoordinate B T w))
        (A.incidenceTor B (A.exteriorIncidenceOriginalCoordinate B T w) n) *
      Module.length
        (((A.exteriorIdentityGenerator T).incidence
          (B.exteriorIdentityGenerator T)).presheaf.stalk w)
        (Koszul.coefficientClosedFiber
          ((A.exteriorIncidenceOriginalCoordinate B T).stalkMap w).hom) := by
  obtain ⟨s, hs, hker⟩ := Diagonal.exists_regular_kernel_of_smooth Y.hom
    (A.exteriorIncidenceOldMiddlePoint B T w)
  refine (A.exteriorIncidenceTor_length_eq_remaining B T w s hs hker n).trans ?_
  have hlists := A.exteriorIncidenceRemainingList_eq B T w s
  have hchange := congrArg (fun l : List ((A.exteriorParameterDiagonal T B).presheaf.stalk
      (A.exteriorIncidenceToCoefficientQuotient B T w)) =>
    Module.length ((A.exteriorParameterDiagonal T B).presheaf.stalk
        (A.exteriorIncidenceToCoefficientQuotient B T w))
      ((Koszul.coefficientComplex
        (ModuleCat.of ((A.exteriorParameterDiagonal T B).presheaf.stalk
            (A.exteriorIncidenceToCoefficientQuotient B T w))
          ((A.exteriorParameterDiagonal T B).presheaf.stalk
            (A.exteriorIncidenceToCoefficientQuotient B T w))) l).homology n)) hlists
  refine hchange.trans ?_
  let g := Diagonal.baseChangeStalkMap (A.exteriorIncidenceProjection_isPullback B T) w
  have : IsLocalHom g.hom := inferInstanceAs (IsLocalHom
    (StalkTransport.pointedMap (A.exteriorCoefficientQuotientProjection B T)
      (A.exteriorIncidenceToCoefficientQuotient B T w)
      (A.incidenceToSupportProduct B (A.exteriorIncidenceOriginalCoordinate B T w))
      (congrArg (fun f => f w) (A.exteriorIncidenceProjection_isPullback B T).w)).hom)
  refine (Koszul.regularCoefficientFlat_length g.hom
    (Diagonal.baseChangeStalkMap_flat (A.exteriorIncidenceProjection_isPullback B T) w)
    (s.map (A.exteriorIncidenceOriginalMiddleStalkMap B T w).hom) n).trans ?_
  have hold := A.originalTor_length_at_middle B
    (A.exteriorIncidenceOriginalCoordinate B T w) (A.exteriorIncidenceOldMiddlePoint B T w)
    (A.exteriorIncidenceOldMiddlePoint_eq B T w) s hs hker n
  exact congrArg₂ (fun a b : ℕ∞ => a * b) hold.symm
    (A.exteriorIncidenceProjection_closedFiber_length B T w)

/-- Flat projection sends each actual exterior incidence generic to an original generic. -/
def exteriorIncidenceOriginalGeneric
    (w : genericPoints ((A.exteriorIdentityGenerator T).incidence
      (B.exteriorIdentityGenerator T))) : genericPoints (A.incidence B) :=
  ⟨A.exteriorIncidenceOriginalCoordinate B T w.1,
    mem_genericPoints_of_generalizing (A.exteriorIncidenceOriginalCoordinate B T)
      (Flat.generalizingMap _) w.1 w.2⟩

/-- The actual generic closed fiber is a quotient of an Artinian incidence stalk. -/
theorem exteriorIncidenceFiber_length_ne_top
    (w : genericPoints ((A.exteriorIdentityGenerator T).incidence
      (B.exteriorIdentityGenerator T))) :
    Module.length
      (((A.exteriorIdentityGenerator T).incidence
        (B.exteriorIdentityGenerator T)).presheaf.stalk w.1)
      (Koszul.coefficientClosedFiber
        ((A.exteriorIncidenceOriginalCoordinate B T).stalkMap w.1).hom) ≠ ⊤ := by
  have := isArtinianRing_stalk_of_mem_genericPoints w.1 w.2
  exact Module.length_ne_top

/-- The whole local closed-fiber multiplicity, after its finite length has been proved. -/
def exteriorIncidenceFiberMultiplicity
    (w : genericPoints ((A.exteriorIdentityGenerator T).incidence
      (B.exteriorIdentityGenerator T))) : ℤ :=
  LengthEuler.integerLength
    (Koszul.coefficientClosedFiber
      ((A.exteriorIncidenceOriginalCoordinate B T).stalkMap w.1).hom)
    (A.exteriorIncidenceFiber_length_ne_top B T w)

/-- The named actual generic Tor coefficient retains every correction and the
whole local fiber multiplier. No Tor coefficient is replaced by a fundamental multiplicity. -/
theorem exteriorIncidenceTorCoefficient_eq
    (w : genericPoints ((A.exteriorIdentityGenerator T).incidence
      (B.exteriorIdentityGenerator T))) :
    (A.exteriorIdentityGenerator T).incidenceTorCoefficient (S := Spec (.of k))
        (B.exteriorIdentityGenerator T) w =
      A.incidenceTorCoefficient (S := Spec (.of k)) B (A.exteriorIncidenceOriginalGeneric B T w) *
        A.exteriorIncidenceFiberMultiplicity B T w := by
  unfold incidenceTorCoefficient LengthEuler.signedLengthSum
  rw [finsum_mul]
  apply finsum_congr
  intro n
  simp only [LengthEuler.integerLength, A.exteriorIncidenceTor_length B T w.1 n,
    ENat.toNat_mul, Nat.cast_mul, mul_assoc, exteriorIncidenceFiberMultiplicity,
    exteriorIncidenceOriginalGeneric]

end Motivic.FiniteCorrespondenceGenerator
