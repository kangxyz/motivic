/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.FirstStageWeightedRemainingCoefficient

/-!
# Actual original-label weighted remaining coefficient consumers

The first arbitrary-field consumer uses one literal affine point and remaining
list without assuming regularity. The second retains regularity explicitly and
checks actual finite-pushforward Tor coefficients on both sides. Every original
pair-incidence generic is still an independent summand, with its signed Tor
weight and its original incidence residue degree. No injectivity, disjointness,
reducedness, component-lift choice, or supplied comparison equality is assumed.
The third consumer uses the global integral-cycle equality over an arbitrary
field, without choosing an affine chart or supplying a regular list.

Prepared as source-only consumers. These declarations have not been elaborated
or accepted merely by being present in this candidate.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.AlgebraicGeometry.Scheme (IntegralCycle SmoothSite
  isLocallyNoetherian_correspondenceSixfoldAmbient)
open _root_.AlgebraicGeometry.Scheme.Products (correspondenceSixfoldAmbient)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic RingTheory.Sequence
open _root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme
open Motivic.ExteriorImageComponentGeometry
open _root_.HomologicalComplex.ModuleLengthEuler
open scoped BigOperators

universe u

namespace MotivicTest.FirstStageWeightedRemainingCoefficient

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

local instance consumerBaseSeparated :
    ((Functor.fromPUnit (Spec (.of k))).obj X.right).IsSeparated :=
  inferInstanceAs (Spec (.of k)).IsSeparated

local instance consumerBaseNoetherian :
    IsLocallyNoetherian ((Functor.fromPUnit (Spec (.of k))).obj X.right) :=
  inferInstanceAs (IsLocallyNoetherian (Spec (.of k)))

local instance consumerSixfoldNoetherian : IsLocallyNoetherian
    (correspondenceSixfoldAmbient X.hom Y.hom Z.hom W.hom) :=
  isLocallyNoetherian_correspondenceSixfoldAmbient (S := Spec (.of k))
    X.hom Y.hom Z.hom W.hom

local instance consumerImageNoetherian : IsNoetherian (F.leftIntermediateImageProduct G H) :=
  ExteriorImageComponentEulerReplacement.imageProductNoetherian F G H

variable (V : (F.leftIntermediateImageProduct G H).affineOpens)
  (p : Spec Γ(F.leftIntermediateImageProduct G H, V))
  (s : List ((pullback Z.hom Z.hom).presheaf.stalk
    (F.leftImageMiddlePair G H (V.2.fromSpec p))))
  (y : F.leftImageIncidence G H) (hy : y ∈ genericPoints (F.leftImageIncidence G H))
  (hp : V.2.fromSpec p = F.leftImageIncidenceInclusion G H y)
  (hker : (pullback.diagonal Z.hom).ker.stalk
    (F.leftImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s)

/-- The actual outer Euler sum equals the original-label full exterior quotient
sum on exactly the same target stalk, without a regular-list hypothesis. -/
theorem actualWeightedExteriorQuotient :
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
            (_root_.ChainComplex.Koszul.finiteHomology_of_artinian_quotient_of_le_annihilator _
                _ ⊥ bot_le) :=
  F.firstStagePushforwardRemainingOuter_eq_weightedExteriorQuotient G H V p s y hy hp hker

include hy hp hker in
/-- The genuine pushed canonical triple coefficient equals the sum of actual
pushed component-incidence coefficients, retaining the original regular list
and all original signed degree weights without merging colliding labels. -/
theorem actualWeightedRemainingIncidence
    (hsreg : IsRegular ((pullback Z.hom Z.hom).presheaf.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p))) s) :
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
                ((F.smoothIncidenceComponentGenerator k G z).incidenceTorCoefficient H))) y :=
  F.leftImageIncidenceTorCycleCoefficient_eq_weightedRemainingIncidence
    G H V p s y hy hp hsreg hker

/-- The global cycle consumer needs only the three original correspondences
on smooth schemes over an arbitrary field, retaining every original label and
its original signed Tor coefficient and incidence residue degree. -/
theorem actualWeightedRemainingIncidenceCycle :
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
              ((F.smoothIncidenceComponentGenerator k G z).incidenceTorCoefficient H)) :=
  F.leftImageIncidenceTorCycle_eq_weightedRemainingIncidence G H

end MotivicTest.FirstStageWeightedRemainingCoefficient
