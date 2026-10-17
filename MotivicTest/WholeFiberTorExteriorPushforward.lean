/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.WholeFiberTorExteriorPushforward
public import MotivicTest.IntegralExteriorCyclePushforward

/-!
# Actual affine-V whole-Tor exterior pushforward

The endpoint pushes the EXISTING firstStageWholeTorGenericCycle along the
ACTUAL finite leftIntermediateImageMap restricted to the affine target V.
It equals the sum over ALL original pair-incidence generics of signed pair
Tor coefficient times ORIGINAL incidence residue degree times the restricted
imageExterior fundamental cycle, with its actual restricted closed immersion.

All multiplicities remain those of unreduced exterior schemes. The coefficient
consumer sums every image collision; off-generic and empty-source cases are
included. No target normality, separability, or generic-index injectivity is
assumed. This proves no remaining-diagonal, iterated-pairing, or associativity claim.
SOURCE-ONLY PROPOSAL: no compilation or transitive prerequisite acceptance claimed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open MotivicTest.IntegralGenericFiniteImage
open MotivicTest.IntegralExteriorCyclePushforward
open scoped BigOperators

universe u

namespace MotivicTest.WholeFiberTorExteriorPushforward

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)
  (V : (F.leftIntermediateImageProduct G H).affineOpens)

local instance actualWholeSourceNoetherian : IsNoetherian (F.leftIntermediateSupportProduct G H) :=
  isNoetherian_of_finiteType
    (pullback.fst (F.incidenceTarget G ≫ Z.hom) (H.projection ≫ Z.hom))

local instance actualExteriorSourceBaseNoetherian :
    IsNoetherian (pullback X.hom (H.projection ≫ Z.hom)) := by
  let : IsNoetherian ((𝟭 Scheme).obj X.left) :=
    isNoetherian_of_finiteType (Y := Spec (.of k)) X.hom
  exact isNoetherian_of_finiteType (pullback.fst X.hom (H.projection ≫ Z.hom))

local instance actualWholeImageProjectionFinite : IsFinite (F.leftExteriorImageSourceMap G H) :=
  F.isFinite_leftExteriorImageSourceMap k G H

local instance actualWholeImageNoetherian : IsNoetherian (F.leftIntermediateImageProduct G H) :=
  isNoetherian_of_finiteType (F.leftExteriorImageSourceMap G H)

local instance actualImageOpenNoetherian : IsNoetherian V.1.toScheme :=
  isNoetherian_of_finiteType V.1.ι

local instance actualPairExteriorNoetherian (z : genericPoints (F.incidence G)) :
    IsNoetherian (pairExterior F G H z) :=
  isNoetherian_of_finiteType (pairExteriorInclusion F G H z)

local instance actualImageExteriorNoetherian (z : genericPoints (F.incidence G)) :
    IsNoetherian (imageExterior F G H z) :=
  isNoetherian_of_finiteType (imageExteriorInclusion F G H z)

local instance actualImageExteriorOpenNoetherian (z : genericPoints (F.incidence G)) :
    IsNoetherian (imageExteriorInclusion F G H z ⁻¹ᵁ V).toScheme :=
  isNoetherian_of_finiteType (imageExteriorInclusion F G H z ∣_ V)

/-- The source support inclusion followed by the actual restricted finite map
is literally the restriction of the original composite. -/
theorem actualRestrictedComponentComposition (z : genericPoints (F.incidence G)) :
    (pairExteriorInclusion F G H z ∣_ ((F.leftIntermediateImageMap G H) ⁻¹ᵁ V)) ≫
        (F.leftIntermediateImageMap G H ∣_ V) =
      (pairExteriorInclusion F G H z ≫ F.leftIntermediateImageMap G H) ∣_ V :=
  (morphismRestrict_comp (pairExteriorInclusion F G H z)
    (F.leftIntermediateImageMap G H) V.1).symm

/-- The restricted whole map retains its ORIGINAL residue degree at every point. -/
theorem actualRestrictedWholeResidueDegree (w : F.firstStageWholeOpen G H V) :
    (F.leftIntermediateImageMap G H ∣_ V).residueDegree w =
      (F.leftIntermediateImageMap G H).residueDegree w.1 :=
  FiniteSupportCycle.residueDegree_morphismRestrict _ _ w

/-- The global input is exactly the previously proved signed original-pair
exterior sum, rather than an assumed identity for the whole Tor cycle. -/
theorem actualOriginalExteriorCycle_pushforward :
    letI := IntegralCycle.genericPointFintype (F.incidence G)
    IntegralCycle.finitePushforward (F.leftIntermediateImageMap G H)
        (F.firstStageOriginalExteriorCycle G H) =
      ∑ z : genericPoints (F.incidence G),
        (F.incidenceTorCoefficient (S := Spec (.of k)) G z *
          ((F.incidenceMap G).residueDegree z.1 : ℤ)) •
            IntegralCycle.finitePushforward (imageExteriorInclusion F G H z)
              (fundamentalCycle (imageExterior F G H z)) :=
  actualPairTorExterior_pushforward_sum F G H

/-- Exact affine-open endpoint: the actual whole first-stage Tor cycle pushes
to all ORIGINAL signed pair weights and degrees on the actual restricted
image exteriors, retaining their complete nonreduced fundamental cycles. -/
theorem actualWholeTorPushforward_eq_restrictedImageExteriorSum :
    letI := IntegralCycle.genericPointFintype (F.incidence G)
    IntegralCycle.finitePushforward (F.leftIntermediateImageMap G H ∣_ V)
        (F.firstStageWholeTorGenericCycle G H V) =
      ∑ z : genericPoints (F.incidence G),
        (F.incidenceTorCoefficient (S := Spec (.of k)) G z *
          ((F.incidenceMap G).residueDegree z.1 : ℤ)) •
            IntegralCycle.finitePushforward (imageExteriorInclusion F G H z ∣_ V)
              (fundamentalCycle (imageExteriorInclusion F G H z ⁻¹ᵁ V).toScheme) := by
  classical
  let := IntegralCycle.genericPointFintype (F.incidence G)
  rw [F.firstStageWholeTorGenericCycle_finitePushforward_eq_openRestriction G H V,
    actualOriginalExteriorCycle_pushforward, map_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [map_zsmul, IntegralCycle.openRestriction_finitePushforward_fundamentalCycle]

/-- Coefficients are full sums over original labels, so arbitrary image
collisions and cancellation of negative Tor weights remain visible. -/
theorem actualWholeTorPushforward_allPointCoefficient (y : V.1.toScheme) :
    letI := IntegralCycle.genericPointFintype (F.incidence G)
    IntegralCycle.toPoints
        (IntegralCycle.finitePushforward (F.leftIntermediateImageMap G H ∣_ V)
          (F.firstStageWholeTorGenericCycle G H V)) y =
      ∑ z : genericPoints (F.incidence G),
        (F.incidenceTorCoefficient (S := Spec (.of k)) G z *
          ((F.incidenceMap G).residueDegree z.1 : ℤ)) *
            IntegralCycle.toPoints
              (IntegralCycle.finitePushforward (imageExteriorInclusion F G H z ∣_ V)
                (fundamentalCycle (imageExteriorInclusion F G H z ⁻¹ᵁ V).toScheme)) y := by
  rw [actualWholeTorPushforward_eq_restrictedImageExteriorSum]
  simp only [map_sum, map_zsmul, Finsupp.finsetSum_apply, Finsupp.smul_apply, Int.zsmul_eq_mul]

/-- The actual image-exterior sum has zero coefficient at EVERY nongeneric
point of V, by proved whole-map geometry rather than a claim about finite maps. -/
theorem actualRestrictedImageExteriorSum_offGeneric
    (y : V.1.toScheme) (hy : y ∉ genericPoints V.1.toScheme) :
    letI := IntegralCycle.genericPointFintype (F.incidence G)
    IntegralCycle.toPoints
      (∑ z : genericPoints (F.incidence G),
        (F.incidenceTorCoefficient (S := Spec (.of k)) G z *
          ((F.incidenceMap G).residueDegree z.1 : ℤ)) •
            IntegralCycle.finitePushforward (imageExteriorInclusion F G H z ∣_ V)
              (fundamentalCycle (imageExteriorInclusion F G H z ⁻¹ᵁ V).toScheme)) y = 0 := by
  rw [← actualWholeTorPushforward_eq_restrictedImageExteriorSum]
  exact F.firstStageWholeTorGenericCycle_finitePushforward_offGeneric G H V y hy

/-- Empty original incidence gives zero actual affine-open pushforward;
there is no nonempty-component or chosen-branch premise. -/
theorem actualWholeTorPushforward_empty [IsEmpty (F.incidence G)] :
    IntegralCycle.finitePushforward (F.leftIntermediateImageMap G H ∣_ V)
      (F.firstStageWholeTorGenericCycle G H V) = 0 := by
  rw [actualWholeTorPushforward_eq_restrictedImageExteriorSum]
  simp only [Finset.univ_eq_empty, Finset.sum_empty]

end MotivicTest.WholeFiberTorExteriorPushforward
