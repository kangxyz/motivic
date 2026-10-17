/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.RightWholeFiberTorExteriorDecomposition

/-!
# Actual right source-cycle decomposition consumers over an arbitrary field

The endpoint names the existing right whole Tor cycle on its identical actual
inverse-image open, and the literal right products F.scheme times the ORIGINAL
G,H point closures. Scalar-square and length consumers specify the actual
nonreduced right closed fiber under product symmetry. The sum retains every
original generic label without assuming distinct image supports, unique exterior
branches, connectedness, perfectness, or reduced exterior products.

This pair is source-only; no elaboration, diagnostic success, or acceptance is
claimed. Image-degree balance, the remaining diagonal, and associativity are
outside these consumers.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open Motivic.WholeFiberTorExteriorDecomposition
open scoped BigOperators

universe u

namespace MotivicTest.RightWholeFiberTorExteriorDecomposition

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)
  (V : (F.rightIntermediateImageProduct G H).affineOpens)

local instance actualFirstFactorFlat : Flat (F.targetProjection ≫ Y.hom) := by
  let : Subsingleton (Spec (.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  let : IsIntegral (Spec (.of k)) := inferInstance
  exact Flat.instOfSubsingletonCarrierCarrierCommRingCatOfIsIntegral
    (Y := Spec (.of k)) (F.targetProjection ≫ Y.hom)

local instance actualSwappedOpenNoetherian :
    IsNoetherian (F.rightFirstStageSwappedOpen G H V) :=
  isNoetherian_of_finiteType (F.rightFirstStageWholeSymmetry G H V)

local instance actualRightComponentOpenNoetherian (z : genericPoints (G.incidence H)) :
    IsNoetherian (F.rightFirstStageComponentExteriorInclusion G H z ⁻¹ᵁ
      ((F.rightIntermediateImageMap G H) ⁻¹ᵁ V)).toScheme :=
  isNoetherian_of_finiteType (F.rightFirstStageComponentExteriorInclusion G H z ∣_
    ((F.rightIntermediateImageMap G H) ⁻¹ᵁ V))

/-- The source has the original right factor order and is not reduced after base change. -/
theorem actualRightComponent (z : genericPoints (G.incidence H)) :
    F.rightFirstStageComponentExterior G H z =
      pullback (F.targetProjection ≫ Y.hom)
        ((IntegralClosedSubscheme.pointClosure z.1).val.subschemeι ≫
          G.incidenceSource H ≫ Y.hom) := rfl

/-- The map is the literal closed inclusion, not a finite-image replacement. -/
theorem actualRightComponentInclusion (z : genericPoints (G.incidence H)) :
    F.rightFirstStageComponentExteriorInclusion G H z =
      pullback.map _ _ _ _ (𝟙 F.scheme)
        (IntegralClosedSubscheme.pointClosure z.1).val.subschemeι (𝟙 (Spec (.of k)))
        (by simp) (by simp) := rfl

/-- The original point-closure ideal is pulled back by the actual right projection. -/
theorem actualRightComponentSquare (z : genericPoints (G.incidence H)) :
    IsPullback
      (pullback.snd (F.targetProjection ≫ Y.hom)
        ((IntegralClosedSubscheme.pointClosure z.1).val.subschemeι ≫
          G.incidenceSource H ≫ Y.hom))
      (F.rightFirstStageComponentExteriorInclusion G H z)
      (IntegralClosedSubscheme.pointClosure z.1).val.subschemeι
      (F.rightExteriorPairProjection G H) :=
  F.rightFirstStageComponentExteriorInclusion_isPullback G H z

/-- Product symmetry compares the original projection scalar maps as arrows. -/
def actualSymmetryStalkArrow
    (w : (pullback (G.incidenceSource H ≫ Y.hom)
      (F.targetProjection ≫ Y.hom) : Scheme.{u})) :
    Arrow.mk ((F.rightExteriorPairProjection G H).stalkMap
      ((F.rightFirstStageExteriorSymmetry G H).hom w)) ≅
    Arrow.mk ((pullback.fst (G.incidenceSource H ≫ Y.hom)
      (F.targetProjection ≫ Y.hom)).stalkMap w) :=
  F.rightExteriorSymmetryStalkArrowIso G H w

/-- The quotient comparison explicitly retains the original symmetry scalar map. -/
theorem actualClosedFiberScalarSquare
    (w : (pullback (G.incidenceSource H ≫ Y.hom)
      (F.targetProjection ≫ Y.hom) : Scheme.{u})) :
    (F.rightExteriorClosedFiberSymmetryEquiv G H w).toRingHom.comp (Ideal.Quotient.mk _) =
      (Ideal.Quotient.mk _).comp
        ((F.rightFirstStageExteriorSymmetry G H).hom.stalkMap w).hom :=
  F.rightExteriorClosedFiberSymmetryEquiv_scalarSquare G H w

/-- This is the actual right nonreduced closed-fiber length over its original ring. -/
theorem actualClosedFiberLength
    (w : (pullback (G.incidenceSource H ≫ Y.hom)
      (F.targetProjection ≫ Y.hom) : Scheme.{u})) :
    Module.length ((F.rightIntermediateSupportProduct G H).presheaf.stalk
        ((F.rightFirstStageExteriorSymmetry G H).hom w))
      (F.rightExteriorClosedFiber G H ((F.rightFirstStageExteriorSymmetry G H).hom w)) =
    Module.length ((pullback (G.incidenceSource H ≫ Y.hom)
        (F.targetProjection ≫ Y.hom) : Scheme.{u}).presheaf.stalk w)
      (Koszul.coefficientClosedFiber ((pullback.fst (G.incidenceSource H ≫ Y.hom)
        (F.targetProjection ≫ Y.hom)).stalkMap w).hom) :=
  F.rightExteriorClosedFiberSymmetry_length G H w

/-- Every original pair label survives before any finite image or collision grouping. -/
theorem actualOriginalPairLabel
    (w : genericPoints (F.rightFirstStageSwappedOpen G H V)) :
    F.rightFirstStageWholeGenericPair G H V
      (mapGenericPoint (F.rightFirstStageWholeSymmetry G H V) w) =
    componentGeneric (G.incidenceSource H ≫ Y.hom) (F.targetProjection ≫ Y.hom)
      ((F.rightFirstStageExteriorSymmetry G H).hom ⁻¹ᵁ
        ((F.rightIntermediateImageMap G H) ⁻¹ᵁ V)) w :=
  F.rightFirstStageWholeGenericPair_symmetry G H V w

/-- Exact requested endpoint: the existing cycle is the restriction of the whole
sum of actual right exterior fundamental cycles, with original signed G,H weights. -/
theorem actualWholeTorCycle_eq_restriction_originalExteriorSum :
    letI := IntegralCycle.genericPointFintype (G.incidence H)
    F.rightFirstStageWholeTorGenericCycle G H V =
      IntegralCycle.openRestriction ((F.rightIntermediateImageMap G H) ⁻¹ᵁ V)
        (∑ z : genericPoints (G.incidence H),
          G.incidenceTorCoefficient (S := Spec (.of k)) H z •
            IntegralCycle.finitePushforward (F.rightFirstStageComponentExteriorInclusion G H z)
              (fundamentalCycle (F.rightFirstStageComponentExterior G H z))) :=
  F.rightFirstStageWholeTorGenericCycle_eq_openRestriction_originalExteriorCycle G H V

/-- Equivalently, restrict each literal source inclusion to that same whole open.
Every exterior branch contributes its complete unreduced generic multiplicity. -/
theorem actualWholeTorCycle_eq_originalRestrictedExteriorSum :
    letI := IntegralCycle.genericPointFintype (G.incidence H)
    F.rightFirstStageWholeTorGenericCycle G H V =
      ∑ z : genericPoints (G.incidence H),
        G.incidenceTorCoefficient (S := Spec (.of k)) H z •
          IntegralCycle.finitePushforward
            (F.rightFirstStageComponentExteriorInclusion G H z ∣_
              ((F.rightIntermediateImageMap G H) ⁻¹ᵁ V))
            (fundamentalCycle (F.rightFirstStageComponentExteriorInclusion G H z ⁻¹ᵁ
              ((F.rightIntermediateImageMap G H) ⁻¹ᵁ V)).toScheme) := by
  classical
  let := IntegralCycle.genericPointFintype (G.incidence H)
  rw [actualWholeTorCycle_eq_restriction_originalExteriorSum, map_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [map_zsmul, IntegralCycle.openRestriction_finitePushforward_fundamentalCycle]

/-- All-point coefficients retain the original label sum, so no injectivity
hypothesis on any future finite-image map is concealed in the source identity. -/
theorem actualWholeTorCycle_allPointCoefficient (w : F.rightFirstStageWholeOpen G H V) :
    letI := IntegralCycle.genericPointFintype (G.incidence H)
    IntegralCycle.toPoints (F.rightFirstStageWholeTorGenericCycle G H V) w =
      ∑ z : genericPoints (G.incidence H),
        G.incidenceTorCoefficient (S := Spec (.of k)) H z *
          IntegralCycle.toPoints
            (IntegralCycle.finitePushforward
              (F.rightFirstStageComponentExteriorInclusion G H z ∣_
                ((F.rightIntermediateImageMap G H) ⁻¹ᵁ V))
              (fundamentalCycle (F.rightFirstStageComponentExteriorInclusion G H z ⁻¹ᵁ
                ((F.rightIntermediateImageMap G H) ⁻¹ᵁ V)).toScheme)) w := by
  rw [actualWholeTorCycle_eq_originalRestrictedExteriorSum]
  simp only [map_sum, map_zsmul, Finsupp.finsetSum_apply, Finsupp.smul_apply, Int.zsmul_eq_mul]

/-- The entire restricted source sum vanishes at every nongeneric whole-open point. -/
theorem actualExteriorRestriction_offGeneric
    (w : F.rightFirstStageWholeOpen G H V)
    (hw : w ∉ genericPoints (F.rightFirstStageWholeOpen G H V)) :
    IntegralCycle.toPoints
      (IntegralCycle.openRestriction ((F.rightIntermediateImageMap G H) ⁻¹ᵁ V)
        (F.rightFirstStageOriginalExteriorCycle G H)) w = 0 := by
  rw [← F.rightFirstStageWholeTorGenericCycle_eq_openRestriction_originalExteriorCycle G H V,
    FiniteCorrespondenceGenerator.rightFirstStageWholeTorGenericCycle,
    IntegralCycle.toPoints_ofGenericCoefficients_apply, dite_eq_right hw]

/-- Empty original pair incidence contributes zero, with no selected generic branch. -/
theorem actualWholeTorCycle_empty [IsEmpty (G.incidence H)] :
    F.rightFirstStageWholeTorGenericCycle G H V = 0 := by
  rw [actualWholeTorCycle_eq_restriction_originalExteriorSum]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, map_zero]

end MotivicTest.RightWholeFiberTorExteriorDecomposition
