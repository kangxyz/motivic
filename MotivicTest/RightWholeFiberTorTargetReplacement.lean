/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.RightWholeFiberTorTargetReplacement
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Noetherian
public import Motivic.AlgebraicGeometry.Correspondences.Noetherian

/-!
# Original smooth-site right target replacement consumers

All ambient and target Noetherian hypotheses are derived from the actual
smooth finite-type geometry. The tested equalities retain the original finite
pushforward stalk, one remaining list, its exact final-incidence support and
one common zero support ideal in every degree. No cycle coefficient is supplied.
The last consumer also constructs the chart and the common remaining list
from the original generic right final-incidence point. All gates remain pending.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.MotivicTest.RightWholeFiberTorTargetReplacement
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

/-- The last-pair image is closed in the actual smooth Y-times-W product.
Its product with the original first support is locally finite type over that
image, giving the right target Noetherian hypothesis geometrically. -/
local instance : IsLocallyNoetherian (F.rightIntermediateImageProduct G H) := by
  have : IsLocallyNoetherian Y.left :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := Spec (.of K)) Y.hom
  have : IsLocallyNoetherian (pullback Y.hom W.hom) :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := Y.left) (pullback.fst Y.hom W.hom)
  have : IsLocallyNoetherian (G.incidenceMap H).image :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := pullback Y.hom W.hom)
      (G.incidenceMap H).imageι
  exact LocallyOfFiniteType.isLocallyNoetherian (Y := (G.incidenceMap H).image)
    (pullback.snd (F.targetProjection ≫ Y.hom)
      ((G.incidenceMap H).imageι ≫ pullback.fst Y.hom W.hom ≫ Y.hom))

variable (V : (F.rightIntermediateImageProduct G H).affineOpens)
  (p : Spec Γ(F.rightIntermediateImageProduct G H, V))

/-- Finite generation is proved for the literal original pushed sheaf stalk. -/
theorem actualTargetCoefficientFinite (n : ℕ) :
    Module.Finite ((F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p))
      (F.rightFirstStagePushforwardCoefficient (S := Spec (.of K)) G H V p n) :=
  F.rightFirstStagePushforwardCoefficient_finite (S := Spec (.of K)) G H V p n

/-- The actual target coefficient admits genuine fixed-support replacement. -/
theorem actualTargetDegreeReplacement
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (F.rightImageMiddlePair G H (V.2.fromSpec p))))
    (y : F.rightImageIncidence G H) (hy : y ∈ genericPoints (F.rightImageIncidence G H))
    (hp : V.2.fromSpec p = F.rightImageIncidenceInclusion G H y)
    (hs : (pullback.diagonal Y.hom).ker.stalk
      (F.rightImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s) (n : ℕ) :
    letI := F.rightTargetRemainingList_support_isArtinian G H (V.2.fromSpec p) y hy hp s hs
    F.rightFirstStagePushforwardRemainingEuler (S := Spec (.of K)) G H V p s y hy hp hs n =
      ∑ᶠ q : minimalPrimes
          ((F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p)),
        F.rightFirstStagePushforwardGenericLength (S := Spec (.of K)) G H V p n q *
          chainEuler (_root_.ChainComplex.Koszul.coefficientComplex
            (ModuleCat.of ((F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p))
              (((F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p)) ⧸ q.1))
            (F.rightTargetRemainingList G H (V.2.fromSpec p) s))
            (_root_.ChainComplex.Koszul.fixedSupport_prime_finiteHomology
              (F.rightTargetRemainingList G H (V.2.fromSpec p) s) ⊥ q.1 q.2.le) :=
  F.rightFirstStagePushforwardRemainingEuler_replacement (S := Spec (.of K))
    G H V p s y hy hp hs n

/-- The complete original signed outer sum has one common target generic index. -/
theorem actualTargetOuterReplacement
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (F.rightImageMiddlePair G H (V.2.fromSpec p))))
    (y : F.rightImageIncidence G H) (hy : y ∈ genericPoints (F.rightImageIncidence G H))
    (hp : V.2.fromSpec p = F.rightImageIncidenceInclusion G H y)
    (hs : (pullback.diagonal Y.hom).ker.stalk
      (F.rightImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s) :
    letI := F.rightTargetRemainingList_support_isArtinian G H (V.2.fromSpec p) y hy hp s hs
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
      F.rightFirstStagePushforwardRemainingEuler (S := Spec (.of K)) G H V p s y hy hp hs n) =
      ∑ᶠ q : minimalPrimes
          ((F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p)),
        F.rightFirstStagePushforwardGenericEuler (S := Spec (.of K)) G H V p q *
          chainEuler (_root_.ChainComplex.Koszul.coefficientComplex
            (ModuleCat.of ((F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p))
              (((F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p)) ⧸ q.1))
            (F.rightTargetRemainingList G H (V.2.fromSpec p) s))
            (_root_.ChainComplex.Koszul.fixedSupport_prime_finiteHomology
              (F.rightTargetRemainingList G H (V.2.fromSpec p) s) ⊥ q.1 q.2.le) :=
  F.rightFirstStagePushforwardRemainingOuter_replacement (S := Spec (.of K))
    G H V p s y hy hp hs

/-- The same geometrically constructed outer bound applies at every target generic prime. -/
theorem actualTargetGenericBound :
    ∃ b : ℕ, ∀ n, b ≤ n → ∀ q,
      F.rightFirstStagePushforwardGenericLength (S := Spec (.of K)) G H V p n q = 0 :=
  F.rightFirstStagePushforwardGenericLength_exists_bound (S := Spec (.of K)) G H V p

/-- The exact target support index retains the original global specialization. -/
theorem actualTargetGenericIndex
    (q : {q : genericPoints (F.rightIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p}) :
    ((F.rightFirstStageTargetGenericEquiv (S := Spec (.of K)) G H V p).symm q).1 =
      (genericStalkLocalizationPrime (F.rightIntermediateImageProduct G H)
        (V.2.fromSpec p) q).asIdeal :=
  F.rightFirstStageTargetGenericEquiv_symm_val (S := Spec (.of K)) G H V p q

/-- The complete geometric target replacement retains the literal global
component index and its original local prime in each reduced-component factor. -/
theorem actualTargetGlobalReplacement
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (F.rightImageMiddlePair G H (V.2.fromSpec p))))
    (y : F.rightImageIncidence G H) (hy : y ∈ genericPoints (F.rightImageIncidence G H))
    (hp : V.2.fromSpec p = F.rightImageIncidenceInclusion G H y)
    (hs : (pullback.diagonal Y.hom).ker.stalk
      (F.rightImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s) :
    letI := F.rightTargetRemainingList_support_isArtinian G H (V.2.fromSpec p) y hy hp s hs
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
      F.rightFirstStagePushforwardRemainingEuler (S := Spec (.of K)) G H V p s y hy hp hs n) =
      ∑ᶠ q : {q : genericPoints (F.rightIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p},
        F.rightFirstStagePushforwardGenericEuler (S := Spec (.of K)) G H V p
            ((F.rightFirstStageTargetGenericEquiv (S := Spec (.of K)) G H V p).symm q) *
          chainEuler (_root_.ChainComplex.Koszul.coefficientComplex
            (ModuleCat.of ((F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p))
              (((F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p)) ⧸
                (genericStalkLocalizationPrime (F.rightIntermediateImageProduct G H)
                  (V.2.fromSpec p) q).asIdeal))
            (F.rightTargetRemainingList G H (V.2.fromSpec p) s))
            (_root_.ChainComplex.Koszul.fixedSupport_prime_finiteHomology
              (F.rightTargetRemainingList G H (V.2.fromSpec p) s) ⊥
              (genericStalkLocalizationPrime (F.rightIntermediateImageProduct G H)
                (V.2.fromSpec p) q).asIdeal bot_le) :=
  F.rightFirstStagePushforwardRemainingOuter_globalReplacement (S := Spec (.of K))
    G H V p s y hy hp hs

/-- Isolate the actual geometric chart construction from the dependent Euler endpoint. -/
private theorem actualTargetGeometricChart
    (y : F.rightImageIncidence G H) (hy : y ∈ genericPoints (F.rightImageIncidence G H)) :
    ∃ (V : (F.rightIntermediateImageProduct G H).affineOpens)
      (p : Spec Γ(F.rightIntermediateImageProduct G H, V)),
      V.2.fromSpec p = F.rightImageIncidenceInclusion G H y ∧
      ∃ s : List ((pullback Y.hom Y.hom).presheaf.stalk
        (F.rightImageMiddlePair G H (V.2.fromSpec p))),
        RingTheory.Sequence.IsRegular ((pullback Y.hom Y.hom).presheaf.stalk
          (F.rightImageMiddlePair G H (V.2.fromSpec p))) s ∧
        (pullback.diagonal Y.hom).ker.stalk
          (F.rightImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s := by
  obtain ⟨V, p, hp, s, hreg, hs, _⟩ :=
    F.exists_rightFirstStageWholeRemaining_chart (S := Spec (.of K))
      (f := X.hom) (g := Y.hom) (h := Z.hom) (i := W.hom) G H y hy
  exact ⟨V, p, hp, s, hreg, hs⟩

/-- One actual generic right final-incidence point supplies the chart, the
remaining Y-diagonal list, and its kernel equality for the full signed
replacement. No finite-length or numerical replacement hypothesis is supplied. -/
theorem actualTargetGlobalReplacement_chart
    (y : F.rightImageIncidence G H) (hy : y ∈ genericPoints (F.rightImageIncidence G H)) :
    ∃ (V : (F.rightIntermediateImageProduct G H).affineOpens)
      (p : Spec Γ(F.rightIntermediateImageProduct G H, V))
      (hp : V.2.fromSpec p = F.rightImageIncidenceInclusion G H y)
      (s : List ((pullback Y.hom Y.hom).presheaf.stalk
        (F.rightImageMiddlePair G H (V.2.fromSpec p))))
      (hs : (pullback.diagonal Y.hom).ker.stalk
        (F.rightImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s),
      RingTheory.Sequence.IsRegular ((pullback Y.hom Y.hom).presheaf.stalk
        (F.rightImageMiddlePair G H (V.2.fromSpec p))) s ∧
      letI := F.rightTargetRemainingList_support_isArtinian G H (V.2.fromSpec p) y hy hp s hs
      (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
        F.rightFirstStagePushforwardRemainingEuler (S := Spec (.of K)) G H V p s y hy hp hs n) =
        ∑ᶠ q : {q : genericPoints (F.rightIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p},
          F.rightFirstStagePushforwardGenericEuler (S := Spec (.of K)) G H V p
              ((F.rightFirstStageTargetGenericEquiv (S := Spec (.of K)) G H V p).symm q) *
            chainEuler (_root_.ChainComplex.Koszul.coefficientComplex
              (ModuleCat.of ((F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p))
                (((F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p)) ⧸
                  (genericStalkLocalizationPrime (F.rightIntermediateImageProduct G H)
                    (V.2.fromSpec p) q).asIdeal))
              (F.rightTargetRemainingList G H (V.2.fromSpec p) s))
              (_root_.ChainComplex.Koszul.fixedSupport_prime_finiteHomology
                (F.rightTargetRemainingList G H (V.2.fromSpec p) s) ⊥
                (genericStalkLocalizationPrime (F.rightIntermediateImageProduct G H)
                  (V.2.fromSpec p) q).asIdeal bot_le) := by
  classical
  have hchart := actualTargetGeometricChart K X Y Z W F G H y hy
  let V₀ : (F.rightIntermediateImageProduct G H).affineOpens := Classical.choose hchart
  have hV := Classical.choose_spec hchart
  let p₀ : Spec Γ(F.rightIntermediateImageProduct G H, V₀) := Classical.choose hV
  have hp : V₀.2.fromSpec p₀ = F.rightImageIncidenceInclusion G H y :=
    (Classical.choose_spec hV).1
  have hlist := (Classical.choose_spec hV).2
  let s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (F.rightImageMiddlePair G H (V₀.2.fromSpec p₀))) := Classical.choose hlist
  have hreg : RingTheory.Sequence.IsRegular ((pullback Y.hom Y.hom).presheaf.stalk
      (F.rightImageMiddlePair G H (V₀.2.fromSpec p₀))) s :=
    (Classical.choose_spec hlist).1
  have hs : (pullback.diagonal Y.hom).ker.stalk
      (F.rightImageMiddlePair G H (V₀.2.fromSpec p₀)) = Ideal.ofList s :=
    (Classical.choose_spec hlist).2
  refine ⟨V₀, p₀, hp, s, hs, hreg, ?_⟩
  exact actualTargetGlobalReplacement K X Y Z W F G H V₀ p₀ s y hy hp hs

end Motivic.MotivicTest.RightWholeFiberTorTargetReplacement
