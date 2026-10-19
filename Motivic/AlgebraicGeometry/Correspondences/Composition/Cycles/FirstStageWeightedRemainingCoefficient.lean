/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.FirstStageWeightedExteriorPushforward
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.WholeFiberTorGenericCycleWeight
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.ExteriorImageComponentEulerReplacement
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.ExteriorImageRemainingCycleAttachment
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.WholeFiberTorCycleCoefficient
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.WholeFiberTorRemainingLength
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.ImageIncidenceGenericSupport

/-!
# Original-degree weighted remaining coefficients on the left image incidence

A finite coefficient functional on the actual intermediate-image cycle applies
fixed-support replacement at one original affine point and for one original
remaining list. Applying it to the proved weighted exterior pushforward gives
the sum of the full image-exterior quotient Euler characteristics, indexed by
every original pair-incidence generic and weighted by its signed Tor coefficient
and its original incidence residue degree. The finite sums are exchanged only
after their generic index sets have been made finite.

The regular-list corollary identifies both sides with actual finite-pushforward
Tor-cycle coefficients at a generic point of the left whole image incidence.
Coincident image supports remain separately labelled; no exterior is assumed
reduced or integral. Point extensionality upgrades the coefficient equality to
an equality of integral cycles on the left image incidence: smoothness supplies
the local chart and regular list, while actual finite-to-source generic support
gives vanishing off the generic points. No iterated correspondence identity,
right-hand comparison, or associativity theorem is asserted.

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
open ExteriorImageComponentGeometry
open _root_.HomologicalComplex.ModuleLengthEuler

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

local instance weightedRemainingBaseSeparated :
    ((Functor.fromPUnit (Spec (.of k))).obj X.right).IsSeparated :=
  inferInstanceAs (Spec (.of k)).IsSeparated

local instance weightedRemainingBaseNoetherian :
    IsLocallyNoetherian ((Functor.fromPUnit (Spec (.of k))).obj X.right) :=
  inferInstanceAs (IsLocallyNoetherian (Spec (.of k)))

local instance weightedRemainingSixfoldNoetherian : IsLocallyNoetherian
    (correspondenceSixfoldAmbient X.hom Y.hom Z.hom W.hom) :=
  isLocallyNoetherian_correspondenceSixfoldAmbient (S := Spec (.of k))
    X.hom Y.hom Z.hom W.hom

local instance weightedRemainingSourceBaseNoetherian :
    IsNoetherian (pullback X.hom (H.projection ≫ Z.hom)) := by
  let : IsNoetherian ((𝟭 Scheme).obj X.left) := inferInstanceAs (IsNoetherian X.left)
  exact isNoetherian_of_finiteType (pullback.fst X.hom (H.projection ≫ Z.hom))

local instance weightedRemainingImageProjectionFinite :
    IsFinite (F.leftExteriorImageSourceMap G H) :=
  F.isFinite_leftExteriorImageSourceMap k G H

local instance weightedRemainingImageNoetherian :
    IsNoetherian (F.leftIntermediateImageProduct G H) :=
  isNoetherian_of_finiteType (F.leftExteriorImageSourceMap G H)

local instance weightedRemainingExteriorNoetherian
    (C : IntegralClosedSubscheme (F.incidenceMap G).image) :
    IsNoetherian (exterior F G H C) :=
  isNoetherian_of_finiteType (exteriorInclusion F G H C)

variable (V : (F.leftIntermediateImageProduct G H).affineOpens)
  (p : Spec Γ(F.leftIntermediateImageProduct G H, V))

local instance weightedRemainingImageOpenNoetherian : IsNoetherian V.1.toScheme :=
  isNoetherian_of_finiteType V.1.ι

local instance weightedRemainingExteriorOpenNoetherian
    (C : IntegralClosedSubscheme (F.incidenceMap G).image) :
    IsNoetherian (exteriorInclusion F G H C ⁻¹ᵁ V.1).toScheme :=
  isNoetherian_of_finiteType (exteriorInclusion F G H C ∣_ V.1)

/-- Applying the same finite target coefficient functional to the actual
weighted exterior cycle identity gives the full quotient Euler sum. No
regularity of the original remaining list is needed for this replacement. -/
theorem firstStagePushforwardRemainingOuter_eq_weightedExteriorQuotient
    (s : List ((pullback Z.hom Z.hom).presheaf.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p))))
    (y : F.leftImageIncidence G H) (hy : y ∈ genericPoints (F.leftImageIncidence G H))
    (hp : V.2.fromSpec p = F.leftImageIncidenceInclusion G H y)
    (hker : (pullback.diagonal Z.hom).ker.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s) :
    letI := F.leftTargetRemainingList_support_isArtinian G H (V.2.fromSpec p) y hy hp s hker
    letI := IntegralCycle.genericPointFintype (F.incidence G)
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
      F.firstStagePushforwardRemainingEuler G H V p s y hy hp hker n) =
      ∑ z : genericPoints (F.incidence G),
        (F.incidenceTorCoefficient (S := Spec (.of k)) G z *
          ((F.incidenceMap G).residueDegree z.1 : ℤ)) *
          chainEuler (_root_.ChainComplex.Koszul.coefficientComplex
            (ModuleCat.of ((F.leftIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p))
              (((F.leftIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p)) ⧸
                (exteriorInclusion F G H
                  (pointClosure ((F.incidenceMap G).toImage z.1))).ker.stalk (V.2.fromSpec p)))
            (F.leftTargetRemainingList G H (V.2.fromSpec p) s))
            (_root_.ChainComplex.Koszul.finiteHomology_of_artinian_quotient_of_le_annihilator _ _ ⊥
                bot_le) := by
  classical
  let := F.leftTargetRemainingList_support_isArtinian G H (V.2.fromSpec p) y hy hp s hker
  let := IntegralCycle.genericPointFintype (F.incidence G)
  let := IntegralCycle.genericPointFintype (F.leftIntermediateImageProduct G H)
  let Q := {q : genericPoints (F.leftIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p}
  let : Fintype Q := inferInstance
  let R := (F.leftIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p)
  let t := F.leftTargetRemainingList G H (V.2.fromSpec p) s
  let qV : Q → V.1.toScheme := fun q =>
    ⟨q.1.1, F.firstStagePushforwardGeneric_mem G H V p q⟩
  let E : Q → ℤ := fun q =>
    chainEuler (_root_.ChainComplex.Koszul.coefficientComplex
      (ModuleCat.of R (R ⧸ ((F.firstStageTargetGenericEquiv G H V p).symm q).1)) t)
      (_root_.ChainComplex.Koszul.fixedSupport_prime_finiteHomology t ⊥
        ((F.firstStageTargetGenericEquiv G H V p).symm q).1
        ((F.firstStageTargetGenericEquiv G H V p).symm q).2.le)
  let Λ : IntegralCycle (F.leftIntermediateImageProduct G H) → ℤ := fun c =>
    ∑ q : Q, IntegralCycle.toPoints (IntegralCycle.openRestriction V.1 c) (qV q) * E q
  let c : genericPoints (F.incidence G) → IntegralCycle (F.leftIntermediateImageProduct G H) :=
    fun z => IntegralCycle.finitePushforward
      (exteriorInclusion F G H (pointClosure ((F.incidenceMap G).toImage z.1)))
      (fundamentalCycle (exterior F G H (pointClosure ((F.incidenceMap G).toImage z.1))))
  let a : genericPoints (F.incidence G) → ℤ := fun z =>
    F.incidenceTorCoefficient (S := Spec (.of k)) G z *
      ((F.incidenceMap G).residueDegree z.1 : ℤ)
  have hcycle :
      IntegralCycle.finitePushforward (F.leftIntermediateImageMap G H)
          (F.firstStageOriginalExteriorCycle G H) = ∑ z, a z • c z :=
    F.firstStageOriginalExteriorCycle_finitePushforward_eq_imageExteriorSum G H
  have hcomponent (z : genericPoints (F.incidence G)) :
      Λ (c z) = chainEuler (_root_.ChainComplex.Koszul.coefficientComplex
        (ModuleCat.of R (R ⧸ (exteriorInclusion F G H
          (pointClosure ((F.incidenceMap G).toImage z.1))).ker.stalk (V.2.fromSpec p))) t)
        (_root_.ChainComplex.Koszul.finiteHomology_of_artinian_quotient_of_le_annihilator _ _ ⊥
            bot_le) := by
    dsimp only [Λ, c]
    simp only [IntegralCycle.openRestriction_finitePushforward_fundamentalCycle]
    simpa only [Q, qV, E, R, t, finsum_eq_sum_of_fintype] using
      (ExteriorImageComponentEulerReplacement.remainingEuler_replacement F G H
        (pointClosure ((F.incidenceMap G).toImage z.1)) V p s y hy hp hker).symm
  calc
    _ = ∑ q : Q, F.firstStagePushforwardGenericEuler G H V p
        ((F.firstStageTargetGenericEquiv G H V p).symm q) * E q := by
      simpa only [Q, E, R, t, firstStageTargetGenericEquiv_symm_val,
        finsum_eq_sum_of_fintype] using
        F.firstStagePushforwardRemainingOuter_globalReplacement G H V p s y hy hp hker
    _ = Λ (IntegralCycle.finitePushforward (F.leftIntermediateImageMap G H)
        (F.firstStageOriginalExteriorCycle G H)) := by
      dsimp only [Λ]
      apply Finset.sum_congr rfl
      intro q _
      rw [F.firstStagePushforwardGenericEuler_eq_finitePushforward_coefficient G H V p q,
        F.firstStageWholeTorGenericCycle_finitePushforward_eq_openRestriction G H V]
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

/-- For the same original regular list, the actual pushed canonical triple
Tor coefficient is the original-label sum of actual pushed remaining incidence
Tor coefficients. The original incidence degree and signed pair weight remain
outside each component coefficient; collisions are never discarded. -/
theorem leftImageIncidenceTorCycleCoefficient_eq_weightedRemainingIncidence
    (s : List ((pullback Z.hom Z.hom).presheaf.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p))))
    (y : F.leftImageIncidence G H) (hy : y ∈ genericPoints (F.leftImageIncidence G H))
    (hp : V.2.fromSpec p = F.leftImageIncidenceInclusion G H y)
    (hsreg : IsRegular ((pullback Z.hom Z.hom).presheaf.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p))) s)
    (hker : (pullback.diagonal Z.hom).ker.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s) :
    letI := IntegralCycle.genericPointFintype (F.incidence G)
    IntegralCycle.toPoints
        (IntegralCycle.finitePushforward (F.tripleToLeftImageIncidence G H)
          (F.tripleIncidenceTorCycle k G H)) y =
      ∑ z : genericPoints (F.incidence G),
        (F.incidenceTorCoefficient (S := Spec (.of k)) G z *
          ((F.incidenceMap G).residueDegree z.1 : ℤ)) *
          IntegralCycle.toPoints
            (IntegralCycle.finitePushforward
              (remainingToImage F G H (pointClosure ((F.incidenceMap G).toImage z.1))
                (F.smoothIncidenceComponentGenerator k G z) (smoothComponent_imageKernel k F G z))
              (IntegralCycle.ofGenericCoefficients
                ((F.smoothIncidenceComponentGenerator k G z).incidence H)
                ((F.smoothIncidenceComponentGenerator k G z).incidenceTorCoefficient H))) y := by
  classical
  let := IntegralCycle.genericPointFintype (F.incidence G)
  let := F.leftTargetRemainingList_support_isArtinian G H (V.2.fromSpec p) y hy hp s hker
  refine (F.firstStageRemainingEuler_eq_finitePushforward_tripleTorCycle
    k G H V p y hy hp s hsreg hker).symm.trans ?_
  refine (F.firstStagePushforwardRemainingOuter_eq_weightedExteriorQuotient
    G H V p s y hy hp hker).trans ?_
  apply Finset.sum_congr rfl
  intro z _
  apply congrArg (fun b : ℤ =>
    (F.incidenceTorCoefficient (S := Spec (.of k)) G z *
      ((F.incidenceMap G).residueDegree z.1 : ℤ)) * b)
  exact
    ExteriorImageRemainingCycleAttachment.remainingQuotientEuler_eq_finitePushforward_coefficient
      F G H (pointClosure ((F.incidenceMap G).toImage z.1))
      (F.smoothIncidenceComponentGenerator k G z) (smoothComponent_imageKernel k F G z)
      ⟨y, hy⟩ (V.2.fromSpec p) hp s hsreg hker

/-- The genuine pushed canonical triple Tor cycle is the original-label sum
of pushed remaining incidence Tor cycles. Smoothness supplies the local regular
lists; actual finite-to-source generic support handles every nongeneric point.
No affine chart, regular list, or support hypothesis is supplied by the caller. -/
theorem leftImageIncidenceTorCycle_eq_weightedRemainingIncidence :
    letI := IntegralCycle.genericPointFintype (F.incidence G)
    IntegralCycle.finitePushforward (F.tripleToLeftImageIncidence G H)
        (F.tripleIncidenceTorCycle k G H) =
      ∑ z : genericPoints (F.incidence G),
        (F.incidenceTorCoefficient (S := Spec (.of k)) G z *
          ((F.incidenceMap G).residueDegree z.1 : ℤ)) •
          IntegralCycle.finitePushforward
            (remainingToImage F G H (pointClosure ((F.incidenceMap G).toImage z.1))
              (F.smoothIncidenceComponentGenerator k G z) (smoothComponent_imageKernel k F G z))
            (IntegralCycle.ofGenericCoefficients
              ((F.smoothIncidenceComponentGenerator k G z).incidence H)
              ((F.smoothIncidenceComponentGenerator k G z).incidenceTorCoefficient H)) := by
  classical
  let := IntegralCycle.genericPointFintype (F.incidence G)
  apply IntegralCycle.toPoints_injective
  ext y
  simp only [map_sum, map_zsmul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    zsmul_eq_mul]
  by_cases hy : y ∈ genericPoints (F.leftImageIncidence G H)
  · obtain ⟨V, p, hp, s, hsreg, hker, _⟩ :=
      F.exists_firstStageWholeRemaining_chart G H y hy
    exact F.leftImageIncidenceTorCycleCoefficient_eq_weightedRemainingIncidence
      G H V p s y hy hp hsreg hker
  · rw [F.leftImageIncidenceTorCycleCoefficient_eq_zero_of_not_generic k G H y hy]
    symm
    apply Finset.sum_eq_zero
    intro z _
    rw [ExteriorImageComponentGeometry.remainingToImage_finitePushforward_offGeneric
      k F G H (pointClosure ((F.incidenceMap G).toImage z.1))
      (F.smoothIncidenceComponentGenerator k G z) (smoothComponent_imageKernel k F G z)
      ((F.smoothIncidenceComponentGenerator k G z).incidenceTorCoefficient H) y hy,
      mul_zero]

end Motivic.FiniteCorrespondenceGenerator
