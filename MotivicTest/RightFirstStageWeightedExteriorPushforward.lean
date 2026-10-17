/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.RightFirstStageWeightedExteriorPushforward

/-!
# Arbitrary-field consumers of the actual right weighted exterior pushforward

The consumers use the literal right component/source/image schemes and maps.
They supply no geometric reducedness, separability, connectedness, single-branch,
flatness over Y, injectivity of image labels, or comparison-cycle hypotheses.
The original G,H Tor scalars and incidence degrees are retained, including in
the two-label collision and empty-original-label specializations.

Source-only: these consumers have not been compiled or accepted.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open IntegralClosedSubscheme
open scoped BigOperators

universe u

namespace MotivicTest.RightFirstStageWeightedExteriorPushforward

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

local instance consumer_toImageFinite : IsFinite (G.incidenceMap H).toImage :=
  G.incidenceToImage_isFinite H

/-- The image exterior has the actual right factor order and original structure maps. -/
example (C : IntegralClosedSubscheme (G.incidenceMap H).image) :
    F.rightImageComponentExterior G H C =
      pullback (F.targetProjection ≫ Y.hom)
        (C.val.subschemeι ≫ (G.incidenceMap H).imageι ≫
          pullback.fst Y.hom W.hom ≫ Y.hom) := rfl

/-- The relevant Cartesian square is over the original point-closure map
and uses the SECOND projections, with no generator reversal. -/
example (z : genericPoints (G.incidence H)) :
    IsPullback
      (pullback.snd (F.targetProjection ≫ Y.hom)
        ((pointClosure z.1).val.subschemeι ≫ G.incidenceSource H ≫ Y.hom))
      (F.rightFirstStageComponentExteriorMap G H z)
      (pointClosureMap (G.incidenceMap H).toImage z.1)
      (pullback.snd (F.targetProjection ≫ Y.hom)
        ((pointClosure ((G.incidenceMap H).toImage z.1)).val.subschemeι ≫
          (G.incidenceMap H).imageι ≫ pullback.fst Y.hom W.hom ≫ Y.hom)) :=
  F.rightFirstStageComponentExteriorMap_isPullback G H z

/-- Both routes are literally the same original whole-image morphism. -/
example (z : genericPoints (G.incidence H)) :
    F.rightFirstStageComponentExteriorMap G H z ≫
        F.rightImageComponentExteriorInclusion G H
          (pointClosure ((G.incidenceMap H).toImage z.1)) =
      F.rightFirstStageComponentExteriorInclusion G H z ≫
        F.rightIntermediateImageMap G H :=
  F.rightFirstStageComponentExteriorMap_ambient G H z

/-- The same equality gives the original stalk scalar map, including its canonical
point transport. It does not substitute an unrelated abstract ring identification. -/
example (z : genericPoints (G.incidence H))
    (w : F.rightFirstStageComponentExterior G H z) :
    (F.rightFirstStageComponentExteriorMap G H z ≫
      F.rightImageComponentExteriorInclusion G H
        (pointClosure ((G.incidenceMap H).toImage z.1))).stalkMap w =
      ((F.rightIntermediateImageProduct G H).presheaf.stalkCongr
        (.of_eq (congrArg (fun m => m w)
          (F.rightFirstStageComponentExteriorMap_ambient G H z)))).hom ≫
        (F.rightFirstStageComponentExteriorInclusion G H z ≫
          F.rightIntermediateImageMap G H).stalkMap w :=
  Scheme.Hom.stalkMap_congr_hom _ _ (F.rightFirstStageComponentExteriorMap_ambient G H z) w

/-- Component-to-whole genericity is proved without assuming finite maps preserve generics. -/
example (z : genericPoints (G.incidence H))
    (w : genericPoints (F.rightFirstStageComponentExterior G H z)) :
    F.rightFirstStageComponentExteriorInclusion G H z w.1 ∈
      genericPoints (F.rightIntermediateSupportProduct G H) :=
  F.rightFirstStageComponentExteriorInclusion_mem_genericPoints G H z w

/-- The actual component map preserves every genuine generic branch. -/
example (z : genericPoints (G.incidence H))
    (w : genericPoints (F.rightFirstStageComponentExterior G H z)) :
    F.rightFirstStageComponentExteriorMap G H z w.1 ∈
      genericPoints (F.rightImageComponentExterior G H
        (pointClosure ((G.incidenceMap H).toImage z.1))) :=
  F.rightFirstStageComponentExteriorMap_mem_genericPoints G H z w

/-- Every image-exterior generic dominates its integral-support generic over any field. -/
example (C : IntegralClosedSubscheme (G.incidenceMap H).image)
    (v : genericPoints (F.rightImageComponentExterior G H C)) :
    pullback.snd (F.targetProjection ≫ Y.hom)
        (C.val.subschemeι ≫ (G.incidenceMap H).imageι ≫
          pullback.fst Y.hom W.hom ≫ Y.hom) v.1 = genericPoint C.val.subscheme :=
  F.rightImageComponentExterior_projection_generic G H C v

/-- The degree is the original ambient incidence degree, even after whole-image factorization. -/
example (z : genericPoints (G.incidence H)) :
    (G.incidenceMap H).toImage.residueDegree z.1 = (G.incidenceMap H).residueDegree z.1 :=
  G.rightFirstStageToImage_residueDegree H z

/-- The full source and image fundamental cycles retain their unreduced multiplicities. -/
example (z : genericPoints (G.incidence H)) :
    IntegralCycle.finitePushforward (F.rightFirstStageComponentExteriorMap G H z)
        (fundamentalCycle (F.rightFirstStageComponentExterior G H z)) =
      ((G.incidenceMap H).residueDegree z.1 : ℤ) •
        fundamentalCycle (F.rightImageComponentExterior G H
          (pointClosure ((G.incidenceMap H).toImage z.1))) :=
  F.rightFirstStageComponentExteriorMap_finitePushforward_fundamentalCycle G H z

/-- Arbitrary signed scalars and separate original degrees survive a two-label
collision. No injectivity of the image labels is needed to add their contributions. -/
example (z₁ z₂ : genericPoints (G.incidence H)) (a b : ℤ)
    (himage : (G.incidenceMap H).toImage z₁.1 = (G.incidenceMap H).toImage z₂.1) :
    IntegralCycle.finitePushforward (F.rightIntermediateImageMap G H)
      (a • IntegralCycle.finitePushforward (F.rightFirstStageComponentExteriorInclusion G H z₁)
          (fundamentalCycle (F.rightFirstStageComponentExterior G H z₁)) +
        b • IntegralCycle.finitePushforward (F.rightFirstStageComponentExteriorInclusion G H z₂)
          (fundamentalCycle (F.rightFirstStageComponentExterior G H z₂))) =
      (a * ((G.incidenceMap H).residueDegree z₁.1 : ℤ) +
        b * ((G.incidenceMap H).residueDegree z₂.1 : ℤ)) •
        IntegralCycle.finitePushforward
          (F.rightImageComponentExteriorInclusion G H
            (pointClosure ((G.incidenceMap H).toImage z₂.1)))
          (fundamentalCycle (F.rightImageComponentExterior G H
            (pointClosure ((G.incidenceMap H).toImage z₂.1)))) := by
  rw [map_add, map_zsmul, map_zsmul,
    F.rightFirstStageComponentExterior_finitePushforward_ambient G H z₁,
    F.rightFirstStageComponentExterior_finitePushforward_ambient G H z₂,
    smul_smul, smul_smul, himage, add_smul]

/-- The actual endpoint consumes the EXISTING right source cycle and sums
all original G,H generic labels with their original signed Tor coefficients. -/
example :
    letI := IntegralCycle.genericPointFintype (G.incidence H)
    IntegralCycle.finitePushforward (F.rightIntermediateImageMap G H)
        (F.rightFirstStageOriginalExteriorCycle G H) =
      ∑ z : genericPoints (G.incidence H),
        (G.incidenceTorCoefficient (S := Spec (.of k)) H z *
          ((G.incidenceMap H).residueDegree z.1 : ℤ)) •
          IntegralCycle.finitePushforward
            (F.rightImageComponentExteriorInclusion G H
              (pointClosure ((G.incidenceMap H).toImage z.1)))
            (fundamentalCycle (F.rightImageComponentExterior G H
              (pointClosure ((G.incidenceMap H).toImage z.1)))) :=
  F.rightFirstStageOriginalExteriorCycle_finitePushforward_eq_imageExteriorSum G H

/-- The empty-original-label case requires no selected component or branch. -/
example [IsEmpty (genericPoints (G.incidence H))] :
    IntegralCycle.finitePushforward (F.rightIntermediateImageMap G H)
      (F.rightFirstStageOriginalExteriorCycle G H) = 0 := by
  classical
  let := IntegralCycle.genericPointFintype (G.incidence H)
  rw [F.rightFirstStageOriginalExteriorCycle_finitePushforward_eq_imageExteriorSum G H]
  exact Finset.sum_eq_zero (fun z _ => isEmptyElim z)

end MotivicTest.RightFirstStageWeightedExteriorPushforward
