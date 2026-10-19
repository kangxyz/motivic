/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.RightFirstStageWeightedExteriorPushforward
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.RightWholeFiberTorGenericCycleWeight
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.RightExteriorImageComponentEulerReplacement
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.RightExteriorImageRemainingCycleAttachment
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.RightWholeFiberTorCycleCoefficient
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.RightWholeFiberTorRemainingLength
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.ImageIncidenceGenericSupport

/-!
# Original-degree weighted remaining coefficients on the right image incidence

A finite coefficient functional on the actual intermediate-image cycle applies
fixed-support replacement at one original affine point and for one original
remaining Y list. Applying it to the proved weighted exterior pushforward gives
the sum of the full image-exterior quotient Euler characteristics, indexed by
every original G,H incidence generic and weighted by its signed Tor coefficient
and its original incidence residue degree. The finite sums are exchanged only
after their generic index sets have been made finite.

The regular-list corollary identifies both sides with actual finite-pushforward
Tor-cycle coefficients at a generic point of the right whole image incidence.
Coincident image supports remain separately labelled; no exterior is assumed
reduced or integral. Point extensionality upgrades the coefficient equality to
an equality of integral cycles on the right image incidence: smoothness supplies
the local chart and regular list, while actual finite-to-source generic support
gives vanishing off the generic points. No iterated correspondence identity,
bracket identification or associativity theorem is asserted.

Prepared as a source-only candidate. No compilation, diagnostic success, or
formal acceptance is asserted by this source or its companion consumer.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingTheory.Sequence
open scoped BigOperators

universe u

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Products

open _root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme
open RightExteriorImageComponentGeometry
open _root_.HomologicalComplex.ModuleLengthEuler

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

local instance rightWeightedRemainingBaseSeparated :
    ((Functor.fromPUnit (Spec (.of k))).obj X.right).IsSeparated :=
  inferInstanceAs (Spec (.of k)).IsSeparated

local instance rightWeightedRemainingBaseNoetherian :
    IsLocallyNoetherian ((Functor.fromPUnit (Spec (.of k))).obj X.right) :=
  inferInstanceAs (IsLocallyNoetherian (Spec (.of k)))

local instance rightWeightedRemainingSixfoldNoetherian : IsLocallyNoetherian
    (correspondenceSixfoldAmbient X.hom Y.hom Z.hom W.hom) :=
  isLocallyNoetherian_correspondenceSixfoldAmbient (S := Spec (.of k))
    X.hom Y.hom Z.hom W.hom

local instance weightedRemainingSourceNoetherian :
    IsNoetherian ((𝟭 Scheme).obj X.left) :=
  inferInstanceAs (IsNoetherian X.left)

local instance rightWeightedRemainingSourceBaseNoetherian :
    IsNoetherian (pullback (F.targetProjection ≫ Y.hom) Y.hom) := by
  let : IsNoetherian F.scheme := isNoetherian_of_finiteType F.projection
  exact isNoetherian_of_finiteType (pullback.fst (F.targetProjection ≫ Y.hom) Y.hom)

local instance weightedRemainingIncidenceNoetherian
    (P : FiniteCorrespondenceGenerator Y.hom W.hom) : IsNoetherian (F.incidence P) :=
  isNoetherian_of_finiteType (F.incidenceSource P)

local instance rightWeightedRemainingImageProjectionFinite :
    IsFinite (F.rightExteriorImageSourceMap G H) :=
  F.isFinite_rightExteriorImageSourceMap k G H

local instance rightWeightedRemainingImageNoetherian :
    IsNoetherian (F.rightIntermediateImageProduct G H) :=
  isNoetherian_of_finiteType (F.rightExteriorImageSourceMap G H)

local instance rightWeightedRemainingExteriorNoetherian
    (C : IntegralClosedSubscheme (G.incidenceMap H).image) :
    IsNoetherian (F.rightImageComponentExterior G H C) :=
  isNoetherian_of_finiteType (F.rightImageComponentExteriorInclusion G H C)

variable (V : (F.rightIntermediateImageProduct G H).affineOpens)
  (p : Spec Γ(F.rightIntermediateImageProduct G H, V))

local instance rightWeightedRemainingImageOpenNoetherian : IsNoetherian V.1.toScheme :=
  isNoetherian_of_finiteType V.1.ι

local instance rightWeightedRemainingExteriorOpenNoetherian
    (C : IntegralClosedSubscheme (G.incidenceMap H).image) :
    IsNoetherian (F.rightImageComponentExteriorInclusion G H C ⁻¹ᵁ V.1).toScheme :=
  isNoetherian_of_finiteType (F.rightImageComponentExteriorInclusion G H C ∣_ V.1)

/-- Applying the same finite target coefficient functional to the actual
weighted exterior cycle identity gives the full quotient Euler sum. No
regularity of the original remaining list is needed for this replacement. -/
theorem rightFirstStagePushforwardRemainingOuter_eq_weightedExteriorQuotient
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (F.rightImageMiddlePair G H (V.2.fromSpec p))))
    (y : F.rightImageIncidence G H) (hy : y ∈ genericPoints (F.rightImageIncidence G H))
    (hp : V.2.fromSpec p = F.rightImageIncidenceInclusion G H y)
    (hker : (pullback.diagonal Y.hom).ker.stalk
      (F.rightImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s) :
    letI := F.rightTargetRemainingList_support_isArtinian G H (V.2.fromSpec p) y hy hp s hker
    letI := IntegralCycle.genericPointFintype (G.incidence H)
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
      F.rightFirstStagePushforwardRemainingEuler G H V p s y hy hp hker n) =
      ∑ z : genericPoints (G.incidence H),
        (G.incidenceTorCoefficient (S := Spec (.of k)) H z *
          ((G.incidenceMap H).residueDegree z.1 : ℤ)) *
          chainEuler (_root_.ChainComplex.Koszul.coefficientComplex
            (ModuleCat.of ((F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p))
              (((F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p)) ⧸
                (F.rightImageComponentExteriorInclusion G H
                  (pointClosure ((G.incidenceMap H).toImage z.1))).ker.stalk (V.2.fromSpec p)))
            (F.rightTargetRemainingList G H (V.2.fromSpec p) s))
            (_root_.ChainComplex.Koszul.finiteHomology_of_artinian_quotient_of_le_annihilator _ _ ⊥
                bot_le) := by
  classical
  let := F.rightTargetRemainingList_support_isArtinian G H (V.2.fromSpec p) y hy hp s hker
  let := IntegralCycle.genericPointFintype (G.incidence H)
  let := IntegralCycle.genericPointFintype (F.rightIntermediateImageProduct G H)
  let Q := {q : genericPoints (F.rightIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p}
  let : Fintype Q := inferInstance
  let R := (F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p)
  let t := F.rightTargetRemainingList G H (V.2.fromSpec p) s
  let qV : Q → V.1.toScheme := fun q =>
    ⟨q.1.1, F.rightFirstStagePushforwardGeneric_mem G H V p q⟩
  let E : Q → ℤ := fun q =>
    chainEuler (_root_.ChainComplex.Koszul.coefficientComplex
      (ModuleCat.of R (R ⧸ ((F.rightFirstStageTargetGenericEquiv G H V p).symm q).1)) t)
      (_root_.ChainComplex.Koszul.fixedSupport_prime_finiteHomology t ⊥
        ((F.rightFirstStageTargetGenericEquiv G H V p).symm q).1
        ((F.rightFirstStageTargetGenericEquiv G H V p).symm q).2.le)
  let Λ : IntegralCycle (F.rightIntermediateImageProduct G H) → ℤ := fun c =>
    ∑ q : Q, IntegralCycle.toPoints (IntegralCycle.openRestriction V.1 c) (qV q) * E q
  let c : genericPoints (G.incidence H) → IntegralCycle (F.rightIntermediateImageProduct G H) :=
    fun z => IntegralCycle.finitePushforward
      (F.rightImageComponentExteriorInclusion G H (pointClosure ((G.incidenceMap H).toImage z.1)))
      (fundamentalCycle (F.rightImageComponentExterior G H
        (pointClosure ((G.incidenceMap H).toImage z.1))))
  let a : genericPoints (G.incidence H) → ℤ := fun z =>
    G.incidenceTorCoefficient (S := Spec (.of k)) H z *
      ((G.incidenceMap H).residueDegree z.1 : ℤ)
  have hcycle :
      IntegralCycle.finitePushforward (F.rightIntermediateImageMap G H)
          (F.rightFirstStageOriginalExteriorCycle G H) = ∑ z, a z • c z :=
    F.rightFirstStageOriginalExteriorCycle_finitePushforward_eq_imageExteriorSum G H
  have hcomponent (z : genericPoints (G.incidence H)) :
      Λ (c z) = chainEuler (_root_.ChainComplex.Koszul.coefficientComplex
        (ModuleCat.of R (R ⧸ (F.rightImageComponentExteriorInclusion G H
          (pointClosure ((G.incidenceMap H).toImage z.1))).ker.stalk (V.2.fromSpec p))) t)
        (_root_.ChainComplex.Koszul.finiteHomology_of_artinian_quotient_of_le_annihilator _ _ ⊥
            bot_le) := by
    dsimp only [Λ, c]
    simp only [IntegralCycle.openRestriction_finitePushforward_fundamentalCycle]
    simpa only [Q, qV, E, R, t, finsum_eq_sum_of_fintype] using
      (RightExteriorImageComponentEulerReplacement.remainingEuler_replacement F G H
        (pointClosure ((G.incidenceMap H).toImage z.1)) V p s y hy hp hker).symm
  calc
    _ = ∑ q : Q, F.rightFirstStagePushforwardGenericEuler G H V p
        ((F.rightFirstStageTargetGenericEquiv G H V p).symm q) * E q := by
      simpa only [Q, E, R, t, rightFirstStageTargetGenericEquiv_symm_val,
        finsum_eq_sum_of_fintype] using
        F.rightFirstStagePushforwardRemainingOuter_globalReplacement G H V p s y hy hp hker
    _ = Λ (IntegralCycle.finitePushforward (F.rightIntermediateImageMap G H)
        (F.rightFirstStageOriginalExteriorCycle G H)) := by
      dsimp only [Λ]
      apply Finset.sum_congr rfl
      intro q _
      rw [F.rightFirstStagePushforwardGenericEuler_eq_finitePushforward_coefficient G H V p q,
        F.rightFirstStageWholeTorGenericCycle_eq_openRestriction_originalExteriorCycle G H V,
        ← IntegralCycle.openRestriction_finitePushforward]
    _ = Λ (∑ z, a z • c z) := congrArg Λ hcycle
    _ = ∑ z, a z * Λ (c z) := by
      dsimp only [Λ]
      simp only [map_sum, map_zsmul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
        zsmul_eq_mul, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      exact mul_assoc _ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z _
      exact congrArg (fun b : ℤ => a z * b) (hcomponent z)

open RightExteriorImageRemainingCycleAttachment
  (remainingQuotientEuler_eq_finitePushforward_coefficient) in
/-- For the same original regular list, the actual pushed canonical triple
Tor coefficient is the original-label sum of actual pushed remaining incidence
Tor coefficients. The original incidence degree and signed pair weight remain
outside each component coefficient; collisions are never discarded. -/
theorem rightImageIncidenceTorCycleCoefficient_eq_weightedRemainingIncidence
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (F.rightImageMiddlePair G H (V.2.fromSpec p))))
    (y : F.rightImageIncidence G H) (hy : y ∈ genericPoints (F.rightImageIncidence G H))
    (hp : V.2.fromSpec p = F.rightImageIncidenceInclusion G H y)
    (hsreg : IsRegular ((pullback Y.hom Y.hom).presheaf.stalk
      (F.rightImageMiddlePair G H (V.2.fromSpec p))) s)
    (hker : (pullback.diagonal Y.hom).ker.stalk
      (F.rightImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s) :
    letI := IntegralCycle.genericPointFintype (G.incidence H)
    IntegralCycle.toPoints
        (IntegralCycle.finitePushforward (F.tripleToRightImageIncidence G H)
          (F.tripleIncidenceTorCycle k G H)) y =
      ∑ z : genericPoints (G.incidence H),
        (G.incidenceTorCoefficient (S := Spec (.of k)) H z *
          ((G.incidenceMap H).residueDegree z.1 : ℤ)) *
          IntegralCycle.toPoints
            (IntegralCycle.finitePushforward
              (remainingToImage F G H (pointClosure ((G.incidenceMap H).toImage z.1))
                (G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z)
                (ExteriorImageComponentGeometry.smoothComponent_imageKernel
                  (X := Y) (Y := Z) (Z := W) k G H z))
              (IntegralCycle.ofGenericCoefficients
                (F.incidence (G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z))
                (F.incidenceTorCoefficient (G.smoothIncidenceComponentGenerator
                    (X := Y) (Y := Z) (Z := W) k H z)))) y := by
  classical
  let := IntegralCycle.genericPointFintype (G.incidence H)
  let := F.rightTargetRemainingList_support_isArtinian G H (V.2.fromSpec p) y hy hp s hker
  refine (F.rightFirstStageRemainingEuler_eq_finitePushforward_tripleTorCycle
    k G H V p y hy hp s hsreg hker).symm.trans ?_
  refine (F.rightFirstStagePushforwardRemainingOuter_eq_weightedExteriorQuotient
    G H V p s y hy hp hker).trans ?_
  apply Finset.sum_congr rfl
  intro z _
  apply congrArg (fun b : ℤ =>
    (G.incidenceTorCoefficient (S := Spec (.of k)) H z *
      ((G.incidenceMap H).residueDegree z.1 : ℤ)) * b)
  exact
    remainingQuotientEuler_eq_finitePushforward_coefficient
      F G H (pointClosure ((G.incidenceMap H).toImage z.1))
      (G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z)
                (ExteriorImageComponentGeometry.smoothComponent_imageKernel
                  (X := Y) (Y := Z) (Z := W) k G H z)
      ⟨y, hy⟩ (V.2.fromSpec p) hp s hsreg hker

/-- The actual remaining closed immersion preserves generic points by its
proved finite-to-source geometry. Its collision sum therefore vanishes away
from the generic target support; finiteness alone is not used to assert this. -/
private theorem rightRemainingToImage_finitePushforward_offGeneric
    (C : IntegralClosedSubscheme (G.incidenceMap H).image)
    (P : FiniteCorrespondenceGenerator Y.hom W.hom)
    (hC : (C.val.subschemeι ≫ (G.incidenceMap H).imageι).ker = P.val)
    (c : genericPoints (F.incidence P) → ℤ)
    (y : F.rightImageIncidence G H) (hy : y ∉ genericPoints (F.rightImageIncidence G H)) :
    IntegralCycle.toPoints
      (IntegralCycle.finitePushforward (remainingToImage F G H C P hC)
        (IntegralCycle.ofGenericCoefficients (F.incidence P) c)) y = 0 := by
  rw [IntegralCycle.toPoints_finitePushforward_ofGenericCoefficients_apply]
  exact IntegralCycle.genericPushforwardCoefficient_eq_zero_of_not_generic
    (remainingToImage F G H C P hC)
    (fun w => remainingToImage_mem_genericPoints F G H C P hC w.1 w.2) c y hy

/-- The genuine pushed canonical triple Tor cycle is the original-label sum
of pushed remaining incidence Tor cycles. Smoothness supplies the local regular
lists; actual finite-to-source generic support handles every nongeneric point.
No affine chart, regular list, or support hypothesis is supplied by the caller. -/
theorem rightImageIncidenceTorCycle_eq_weightedRemainingIncidence :
    letI := IntegralCycle.genericPointFintype (G.incidence H)
    IntegralCycle.finitePushforward (F.tripleToRightImageIncidence G H)
        (F.tripleIncidenceTorCycle k G H) =
      ∑ z : genericPoints (G.incidence H),
        (G.incidenceTorCoefficient (S := Spec (.of k)) H z *
          ((G.incidenceMap H).residueDegree z.1 : ℤ)) •
          IntegralCycle.finitePushforward
            (remainingToImage F G H (pointClosure ((G.incidenceMap H).toImage z.1))
              (G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z)
                (ExteriorImageComponentGeometry.smoothComponent_imageKernel
                  (X := Y) (Y := Z) (Z := W) k G H z))
            (IntegralCycle.ofGenericCoefficients
              (F.incidence (G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z))
              (F.incidenceTorCoefficient (G.smoothIncidenceComponentGenerator
                  (X := Y) (Y := Z) (Z := W) k H z))) := by
  classical
  let := IntegralCycle.genericPointFintype (G.incidence H)
  apply IntegralCycle.toPoints_injective
  ext y
  simp only [map_sum, map_zsmul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    zsmul_eq_mul]
  by_cases hy : y ∈ genericPoints (F.rightImageIncidence G H)
  · obtain ⟨V, p, hp, s, hsreg, hker, _⟩ :=
      F.exists_rightFirstStageWholeRemaining_chart G H y hy
    exact F.rightImageIncidenceTorCycleCoefficient_eq_weightedRemainingIncidence
      G H V p s y hy hp hsreg hker
  · rw [F.rightImageIncidenceTorCycleCoefficient_eq_zero_of_not_generic k G H y hy]
    symm
    apply Finset.sum_eq_zero
    intro z _
    rw [F.rightRemainingToImage_finitePushforward_offGeneric
      G H (pointClosure ((G.incidenceMap H).toImage z.1))
      (G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z)
                (ExteriorImageComponentGeometry.smoothComponent_imageKernel
                  (X := Y) (Y := Z) (Z := W) k G H z)
      (F.incidenceTorCoefficient (G.smoothIncidenceComponentGenerator
          (X := Y) (Y := Z) (Z := W) k H z)) y hy,
      mul_zero]

end Motivic.FiniteCorrespondenceGenerator
