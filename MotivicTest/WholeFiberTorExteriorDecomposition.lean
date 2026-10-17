/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.WholeFiberTorExteriorDecomposition
public import MotivicTest.IntegralGenericFiniteImage

/-!
# Actual affine whole-open consumers for the exterior decomposition

The component sources and immersions here are definitionally the ORIGINAL
pairExterior and pairExteriorInclusion restricted to firstStageWholeOpen V.
The tested endpoint is the existing firstStageWholeTorGenericCycle itself.
Coverage, unique ORIGINAL labels, all scalar maps, generic multiplicities,
off-generic vanishing, and the empty-incidence case are explicit consumers.

Neither this test nor its library identifies an iterated incidenceTorPairing.
The image-exterior pushforward and remaining-diagonal steps remain separate.
SOURCE-ONLY PROPOSAL: these declarations have not been compiled.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open Motivic.WholeFiberTorExteriorDecomposition
open MotivicTest.IntegralGenericFiniteImage
open scoped BigOperators

universe u

namespace MotivicTest.WholeFiberTorExteriorDecomposition

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)
  (V : (F.leftIntermediateImageProduct G H).affineOpens)

local instance wholeExterior_testFactorFlat : Flat (H.projection ≫ Z.hom) := by
  let : Subsingleton (Spec (.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  let : IsIntegral (Spec (.of k)) := inferInstance
  exact Flat.instOfSubsingletonCarrierCarrierCommRingCatOfIsIntegral
    (Y := Spec (.of k)) (H.projection ≫ Z.hom)

/-- No reconstructed support scheme: this is the original component exterior's actual open. -/
theorem actualComponentOpen (z : genericPoints (F.incidence G)) :
    F.firstStageComponentExteriorOpen G H V z =
      (pairExteriorInclusion F G H z ⁻¹ᵁ ((F.leftIntermediateImageMap G H) ⁻¹ᵁ V)).toScheme :=
  rfl

/-- No abstract replacement morphism: this is the original support immersion's restriction. -/
theorem actualComponentInclusion (z : genericPoints (F.incidence G)) :
    F.firstStageComponentExteriorInclusion G H V z =
      pairExteriorInclusion F G H z ∣_ ((F.leftIntermediateImageMap G H) ⁻¹ᵁ V) := rfl

/-- The actual support restriction square is Cartesian. -/
theorem actualRestrictionSquare (z : genericPoints (F.incidence G)) :
    IsPullback (F.firstStageComponentExteriorInclusion G H V z)
      (pairExteriorInclusion F G H z ⁻¹ᵁ ((F.leftIntermediateImageMap G H) ⁻¹ᵁ V)).ι
      ((F.leftIntermediateImageMap G H) ⁻¹ᵁ V).ι (pairExteriorInclusion F G H z) :=
  componentInclusion_isPullback _ _ _ z

/-- The partition ranges over all branches of the ORIGINAL pair exteriors. -/
def actualGenericPartition :
    (Σ z : genericPoints (F.incidence G),
      genericPoints (pairExteriorInclusion F G H z ⁻¹ᵁ
        ((F.leftIntermediateImageMap G H) ⁻¹ᵁ V)).toScheme) ≃
      genericPoints (F.firstStageWholeOpen G H V) :=
  F.firstStageComponentExteriorGenericPartition G H V

/-- Every actual whole-open generic is reached,
including multiple branches over one pair generic. -/
theorem actualAllBranchesCoverage (w : genericPoints (F.firstStageWholeOpen G H V)) :
    ∃ z : genericPoints (F.incidence G),
      ∃ v : genericPoints (F.firstStageComponentExteriorOpen G H V z),
        actualGenericPartition F G H V ⟨z, v⟩ = w := by
  let a := (actualGenericPartition F G H V).symm w
  exact ⟨a.1, a.2, (actualGenericPartition F G H V).apply_symm_apply w⟩

/-- The inverse retains precisely the existing firstStageWholeGenericPair label. -/
theorem actualUniqueOriginalPairLabel (w : genericPoints (F.firstStageWholeOpen G H V)) :
    ((actualGenericPartition F G H V).symm w).1 = F.firstStageWholeGenericPair G H V w :=
  F.firstStageComponentExteriorGenericPartition_symm_fst G H V w

/-- Different ORIGINAL pair labels cannot meet at a source generic point.
This makes no assertion about their finite images, which may coincide. -/
theorem actualDistinctLabelsDisjoint (z z' : genericPoints (F.incidence G)) (h : z ≠ z')
    (v : genericPoints (F.firstStageComponentExteriorOpen G H V z))
    (v' : genericPoints (F.firstStageComponentExteriorOpen G H V z')) :
    actualGenericPartition F G H V ⟨z, v⟩ ≠ actualGenericPartition F G H V ⟨z', v'⟩ := by
  intro heq
  have hz := congrArg (F.firstStageWholeGenericPair G H V) heq
  exact h (by simpa only [actualGenericPartition,
    F.firstStageWholeGenericPair_component G H V] using hz)

/-- Open restriction compares the actual immersion scalar maps as arrows. -/
def actualOpenStalkArrowIso (z : genericPoints (F.incidence G))
    (w : F.firstStageComponentExteriorOpen G H V z) :
    Arrow.mk ((F.firstStageComponentExteriorInclusion G H V z).stalkMap w) ≅
      Arrow.mk ((pairExteriorInclusion F G H z).stalkMap w.1) :=
  componentInclusionStalkArrowIso _ _ _ z w

/-- The ambient quotient retains the literal original support and open numerator maps. -/
theorem actualClosedFiberScalarSquare (z : genericPoints (F.incidence G))
    (w : genericPoints (F.firstStageComponentExteriorOpen G H V z)) :
    (closedFiberOpenEquiv (F.incidenceTarget G ≫ Z.hom) (H.projection ≫ Z.hom)
        ((F.leftIntermediateImageMap G H) ⁻¹ᵁ V) z w).toRingHom.comp (Ideal.Quotient.mk _) =
      ((pairExteriorInclusion F G H z ⁻¹ᵁ
        ((F.leftIntermediateImageMap G H) ⁻¹ᵁ V)).ι.stalkMap w.1).hom.comp
          ((pairExteriorInclusion F G H z).stalkMap w.1.1).hom :=
  closedFiberOpenEquiv_scalarSquare _ _ _ z w

/-- The original all-degree Tor coefficient attaches to the entire nonreduced support stalk. -/
theorem actualTorCoefficient (z : genericPoints (F.incidence G))
    (w : genericPoints (F.firstStageComponentExteriorOpen G H V z)) :
    F.firstStageWholeTorGenericCoefficient G H V (actualGenericPartition F G H V ⟨z, w⟩) =
      F.incidenceTorCoefficient (S := Spec (.of k)) G z * (genericMultiplicity w : ℤ) :=
  F.firstStageWholeTorGenericCoefficient_component G H V z w

/-- The EXISTING whole-open Tor cycle equals the sum of the ORIGINAL restricted
pair-exterior fundamental cycles, weighted by the original signed pair Tor coefficients. -/
theorem actualWholeTorCycle_eq_originalRestrictedExteriorSum :
    letI := IntegralCycle.genericPointFintype (F.incidence G)
    F.firstStageWholeTorGenericCycle G H V =
      ∑ z : genericPoints (F.incidence G),
        F.incidenceTorCoefficient (S := Spec (.of k)) G z •
          IntegralCycle.finitePushforward
            (pairExteriorInclusion F G H z ∣_ ((F.leftIntermediateImageMap G H) ⁻¹ᵁ V))
            (fundamentalCycle (pairExteriorInclusion F G H z ⁻¹ᵁ
              ((F.leftIntermediateImageMap G H) ⁻¹ᵁ V)).toScheme) :=
  F.firstStageWholeTorGenericCycle_eq_componentExterior_sum G H V

/-- The entire component sum has zero coefficient at every nongeneric whole-open point. -/
theorem actualRestrictedExteriorSum_offGeneric
    (w : F.firstStageWholeOpen G H V) (hw : w ∉ genericPoints (F.firstStageWholeOpen G H V)) :
    letI := IntegralCycle.genericPointFintype (F.incidence G)
    IntegralCycle.toPoints
      (∑ z : genericPoints (F.incidence G),
        F.incidenceTorCoefficient (S := Spec (.of k)) G z •
          IntegralCycle.finitePushforward (F.firstStageComponentExteriorInclusion G H V z)
            (fundamentalCycle (F.firstStageComponentExteriorOpen G H V z))) w = 0 := by
  rw [← F.firstStageWholeTorGenericCycle_eq_componentExterior_sum G H V]
  rw [FiniteCorrespondenceGenerator.firstStageWholeTorGenericCycle,
    IntegralCycle.toPoints_ofGenericCoefficients_apply, dite_eq_right hw]

/-- Empty original incidence has zero whole-open Tor cycle; no generic point is chosen. -/
theorem actualWholeTorCycle_empty [IsEmpty (F.incidence G)] :
    F.firstStageWholeTorGenericCycle G H V = 0 := by
  rw [F.firstStageWholeTorGenericCycle_eq_componentExterior_sum G H V]
  simp only [Finset.univ_eq_empty, Finset.sum_empty]

end MotivicTest.WholeFiberTorExteriorDecomposition
