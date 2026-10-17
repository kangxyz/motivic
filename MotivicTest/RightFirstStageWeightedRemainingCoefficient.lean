/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.RightFirstStageWeightedRemainingCoefficient

/-!
# Actual original-label weighted remaining coefficient consumers

The first arbitrary-field consumer uses one literal affine point and remaining
list without assuming regularity. The second retains regularity explicitly and
checks actual finite-pushforward Tor coefficients on both sides. Every original
G,H incidence generic is still an independent summand, with its signed Tor
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic RingTheory.Sequence
open Motivic.IntegralClosedSubscheme Motivic.RightExteriorImageComponentGeometry Motivic.LengthEuler
open scoped BigOperators

universe u

namespace MotivicTest.RightFirstStageWeightedRemainingCoefficient

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

local instance consumerSourceNoetherian : IsNoetherian ((𝟭 Scheme).obj X.left) :=
  inferInstanceAs (IsNoetherian X.left)

local instance consumerIncidenceNoetherian
    (P : FiniteCorrespondenceGenerator Y.hom W.hom) : IsNoetherian (F.incidence P) :=
  isNoetherian_of_finiteType (F.incidenceSource P)

local instance consumerImageNoetherian : IsNoetherian (F.rightIntermediateImageProduct G H) :=
  RightExteriorImageComponentEulerReplacement.imageProductNoetherian F G H

variable (V : (F.rightIntermediateImageProduct G H).affineOpens)
  (p : Spec Γ(F.rightIntermediateImageProduct G H, V))
  (s : List ((pullback Y.hom Y.hom).presheaf.stalk
    (F.rightImageMiddlePair G H (V.2.fromSpec p))))
  (y : F.rightImageIncidence G H) (hy : y ∈ genericPoints (F.rightImageIncidence G H))
  (hp : V.2.fromSpec p = F.rightImageIncidenceInclusion G H y)
  (hker : (pullback.diagonal Y.hom).ker.stalk
    (F.rightImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s)

/-- The actual outer Euler sum equals the original-label full exterior quotient
sum on exactly the same target stalk, without a regular-list hypothesis. -/
theorem actualWeightedExteriorQuotient :
    letI := F.rightTargetRemainingList_support_isArtinian G H (V.2.fromSpec p) y hy hp s hker
    letI := IntegralCycle.genericPointFintype (G.incidence H)
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
      F.rightFirstStagePushforwardRemainingEuler G H V p s y hy hp hker n) =
      ∑ z : genericPoints (G.incidence H),
        (G.incidenceTorCoefficient (S := Spec (.of k)) H z *
          ((G.incidenceMap H).residueDegree z.1 : ℤ)) *
          chainEuler (Koszul.coefficientComplex
            (ModuleCat.of ((F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p))
              (((F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p)) ⧸
                (F.rightImageComponentExteriorInclusion G H
                  (pointClosure ((G.incidenceMap H).toImage z.1))).ker.stalk (V.2.fromSpec p)))
            (F.rightTargetRemainingList G H (V.2.fromSpec p) s))
            (Koszul.finiteHomology_of_artinian_quotient_of_le_annihilator _ _ ⊥ bot_le) :=
  F.rightFirstStagePushforwardRemainingOuter_eq_weightedExteriorQuotient G H V p s y hy hp hker

include hy hp hker in
/-- The genuine pushed canonical triple coefficient equals the sum of actual
pushed component-incidence coefficients, retaining the original regular list
and all original signed degree weights without merging colliding labels. -/
theorem actualWeightedRemainingIncidence
    (hsreg : IsRegular ((pullback Y.hom Y.hom).presheaf.stalk
      (F.rightImageMiddlePair G H (V.2.fromSpec p))) s) :
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
                    (X := Y) (Y := Z) (Z := W) k H z)))) y :=
  F.rightImageIncidenceTorCycleCoefficient_eq_weightedRemainingIncidence
    G H V p s y hy hp hsreg hker

/-- The global cycle consumer needs only the three original correspondences
on smooth schemes over an arbitrary field, retaining every original label and
its original signed Tor coefficient and incidence residue degree. -/
theorem actualWeightedRemainingIncidenceCycle :
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
                  (X := Y) (Y := Z) (Z := W) k H z))) :=
  F.rightImageIncidenceTorCycle_eq_weightedRemainingIncidence G H

end MotivicTest.RightFirstStageWeightedRemainingCoefficient
