/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.WholeFiberTorTargetReplacement
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Noetherian
public import Motivic.AlgebraicGeometry.Correspondences.Noetherian

/-!
# Original smooth-site target replacement consumers

All ambient and target Noetherian hypotheses are derived from the actual
smooth finite-type geometry. The tested equalities retain the original finite
pushforward stalk, one remaining list, its exact final-incidence support and
one common zero support ideal in every degree. No cycle coefficient is supplied.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.MotivicTest.WholeFiberTorTargetReplacement
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Products

open _root_.HomologicalComplex.ModuleLengthEuler

variable (K : Type u) [Field K] (X Y Z W : SmoothSite (Spec (.of K)))
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

/-- Original smooth finite-type geometry makes the six-factor ambient Noetherian. -/
local instance : IsLocallyNoetherian
    (correspondenceSixfoldAmbient X.hom Y.hom Z.hom W.hom) :=
  isLocallyNoetherian_correspondenceSixfoldAmbient (S := Spec (.of K))
    X.hom Y.hom Z.hom W.hom

/-- The actual image is closed in the smooth product; its third-support product
is locally finite type, giving the target Noetherian hypothesis geometrically. -/
local instance : IsLocallyNoetherian (F.leftIntermediateImageProduct G H) := by
  have : IsLocallyNoetherian X.left :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := Spec (.of K)) X.hom
  have : IsLocallyNoetherian (pullback X.hom Z.hom) :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := X.left) (pullback.fst X.hom Z.hom)
  have : IsLocallyNoetherian (F.incidenceMap G).image :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := pullback X.hom Z.hom)
      (F.incidenceMap G).imageι
  exact LocallyOfFiniteType.isLocallyNoetherian (Y := (F.incidenceMap G).image)
    (pullback.fst ((F.incidenceMap G).imageι ≫ pullback.snd X.hom Z.hom ≫ Z.hom)
      (H.projection ≫ Z.hom))

variable (V : (F.leftIntermediateImageProduct G H).affineOpens)
  (p : Spec Γ(F.leftIntermediateImageProduct G H, V))

/-- Finite generation is proved for the literal original pushed sheaf stalk. -/
theorem actualTargetCoefficientFinite (n : ℕ) :
    Module.Finite ((F.leftIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p))
      (F.firstStagePushforwardCoefficient (S := Spec (.of K)) G H V p n) :=
  F.firstStagePushforwardCoefficient_finite (S := Spec (.of K)) G H V p n

/-- The actual target coefficient admits genuine fixed-support replacement. -/
theorem actualTargetDegreeReplacement
    (s : List ((pullback Z.hom Z.hom).presheaf.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p))))
    (y : F.leftImageIncidence G H) (hy : y ∈ genericPoints (F.leftImageIncidence G H))
    (hp : V.2.fromSpec p = F.leftImageIncidenceInclusion G H y)
    (hs : (pullback.diagonal Z.hom).ker.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s) (n : ℕ) :
    letI := F.leftTargetRemainingList_support_isArtinian G H (V.2.fromSpec p) y hy hp s hs
    F.firstStagePushforwardRemainingEuler (S := Spec (.of K)) G H V p s y hy hp hs n =
      ∑ᶠ q : minimalPrimes
          ((F.leftIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p)),
        F.firstStagePushforwardGenericLength (S := Spec (.of K)) G H V p n q *
          chainEuler (_root_.ChainComplex.Koszul.coefficientComplex
            (ModuleCat.of ((F.leftIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p))
              (((F.leftIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p)) ⧸ q.1))
            (F.leftTargetRemainingList G H (V.2.fromSpec p) s))
            (_root_.ChainComplex.Koszul.fixedSupport_prime_finiteHomology
              (F.leftTargetRemainingList G H (V.2.fromSpec p) s) ⊥ q.1 q.2.le) :=
  F.firstStagePushforwardRemainingEuler_replacement (S := Spec (.of K))
    G H V p s y hy hp hs n

/-- The complete original signed outer sum has one common target generic index. -/
theorem actualTargetOuterReplacement
    (s : List ((pullback Z.hom Z.hom).presheaf.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p))))
    (y : F.leftImageIncidence G H) (hy : y ∈ genericPoints (F.leftImageIncidence G H))
    (hp : V.2.fromSpec p = F.leftImageIncidenceInclusion G H y)
    (hs : (pullback.diagonal Z.hom).ker.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s) :
    letI := F.leftTargetRemainingList_support_isArtinian G H (V.2.fromSpec p) y hy hp s hs
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
      F.firstStagePushforwardRemainingEuler (S := Spec (.of K)) G H V p s y hy hp hs n) =
      ∑ᶠ q : minimalPrimes
          ((F.leftIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p)),
        F.firstStagePushforwardGenericEuler (S := Spec (.of K)) G H V p q *
          chainEuler (_root_.ChainComplex.Koszul.coefficientComplex
            (ModuleCat.of ((F.leftIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p))
              (((F.leftIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p)) ⧸ q.1))
            (F.leftTargetRemainingList G H (V.2.fromSpec p) s))
            (_root_.ChainComplex.Koszul.fixedSupport_prime_finiteHomology
              (F.leftTargetRemainingList G H (V.2.fromSpec p) s) ⊥ q.1 q.2.le) :=
  F.firstStagePushforwardRemainingOuter_replacement (S := Spec (.of K))
    G H V p s y hy hp hs

/-- The same geometrically constructed outer bound applies at every target generic prime. -/
theorem actualTargetGenericBound :
    ∃ b : ℕ, ∀ n, b ≤ n → ∀ q,
      F.firstStagePushforwardGenericLength (S := Spec (.of K)) G H V p n q = 0 :=
  F.firstStagePushforwardGenericLength_exists_bound (S := Spec (.of K)) G H V p

/-- The exact target support index retains the original global specialization. -/
theorem actualTargetGenericIndex
    (q : {q : genericPoints (F.leftIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p}) :
    ((F.firstStageTargetGenericEquiv (S := Spec (.of K)) G H V p).symm q).1 =
      (genericStalkLocalizationPrime (F.leftIntermediateImageProduct G H)
        (V.2.fromSpec p) q).asIdeal :=
  F.firstStageTargetGenericEquiv_symm_val (S := Spec (.of K)) G H V p q

/-- The complete geometric target replacement retains the literal global
component index and its original local prime in each reduced-component factor. -/
theorem actualTargetGlobalReplacement
    (s : List ((pullback Z.hom Z.hom).presheaf.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p))))
    (y : F.leftImageIncidence G H) (hy : y ∈ genericPoints (F.leftImageIncidence G H))
    (hp : V.2.fromSpec p = F.leftImageIncidenceInclusion G H y)
    (hs : (pullback.diagonal Z.hom).ker.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s) :
    letI := F.leftTargetRemainingList_support_isArtinian G H (V.2.fromSpec p) y hy hp s hs
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
      F.firstStagePushforwardRemainingEuler (S := Spec (.of K)) G H V p s y hy hp hs n) =
      ∑ᶠ q : {q : genericPoints (F.leftIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p},
        F.firstStagePushforwardGenericEuler (S := Spec (.of K)) G H V p
            ((F.firstStageTargetGenericEquiv (S := Spec (.of K)) G H V p).symm q) *
          chainEuler (_root_.ChainComplex.Koszul.coefficientComplex
            (ModuleCat.of ((F.leftIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p))
              (((F.leftIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p)) ⧸
                (genericStalkLocalizationPrime (F.leftIntermediateImageProduct G H)
                  (V.2.fromSpec p) q).asIdeal))
            (F.leftTargetRemainingList G H (V.2.fromSpec p) s))
            (_root_.ChainComplex.Koszul.fixedSupport_prime_finiteHomology
              (F.leftTargetRemainingList G H (V.2.fromSpec p) s) ⊥
              (genericStalkLocalizationPrime (F.leftIntermediateImageProduct G H)
                (V.2.fromSpec p) q).asIdeal bot_le) :=
  F.firstStagePushforwardRemainingOuter_globalReplacement (S := Spec (.of K))
    G H V p s y hy hp hs

end Motivic.MotivicTest.WholeFiberTorTargetReplacement
