/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.TripleFixedSupportTorComparison
public import Motivic.AlgebraicGeometry.SmoothSiteNoetherian

/-!
# Actual smooth-site fixed-support sums and canonical triple coefficients

The actual middle lists, their final support and both minimal-prime sum
identifications are constructed from the original smooth-site geometry.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingTheory.Sequence
open Motivic.LengthEuler

universe u

namespace Motivic.MotivicTest.TripleFixedSupportTorComparison

variable (k : Type u) [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

set_option backward.isDefEq.respectTransparency false in
/-- Both actual minimal-prime sums from one constructed pair of original
middle lists equal the canonical triple coefficient over any field. -/
theorem actualOriginalFixedSupportSums (w : genericPoints (F.tripleIncidence G H)) :
    letI := isLocallyNoetherian_correspondenceSixfoldAmbient (S := Spec (.of k))
      X.hom Y.hom Z.hom W.hom
    let p := F.tripleIncidenceSixfoldInclusion G H w.val
    ∃ (t : List ((pullback Y.hom Y.hom).presheaf.stalk
        (correspondenceSixfoldFirstMiddlePair X.hom Y.hom Z.hom W.hom p)))
      (s : List ((pullback Z.hom Z.hom).presheaf.stalk
        (correspondenceSixfoldSecondMiddlePair X.hom Y.hom Z.hom W.hom p))),
      let t' := t.map
        ((correspondenceSixfoldFirstMiddlePair X.hom Y.hom Z.hom W.hom).stalkMap p).hom
      let s' := s.map
        ((correspondenceSixfoldSecondMiddlePair X.hom Y.hom Z.hom W.hom).stalkMap p).hom
      ∃ hker : RingHom.ker
        ((correspondenceSecondDiagonalInclusion X.hom Y.hom Z.hom W.hom ≫
          correspondenceFirstDiagonalInclusion X.hom Y.hom Z.hom W.hom).stalkMap
            (F.tripleIncidenceFourfoldInclusion G H w.val)).hom = Ideal.ofList (t' ++ s'),
        letI := F.tripleTwoList_support_isArtinian (S := Spec (.of k)) G H w t' s' hker
        let M := F.tripleIncidenceSupportStalkModule G H w.val
        Koszul.twoListFixedSupportSum M s' t' =
            F.tripleIncidenceTorCoefficient (S := Spec (.of k)) G H w ∧
          letI := Koszul.twoList_swappedArtinian M s' t'
          Koszul.twoListFixedSupportSum M t' s' =
            F.tripleIncidenceTorCoefficient (S := Spec (.of k)) G H w :=
  F.exists_common_fixedSupport_sums (S := Spec (.of k)) G H w

set_option backward.isDefEq.respectTransparency false in
/-- The actual combined diagonal supplies maximal-ideal membership for every
chosen pair of lists generating its genuine kernel, without assuming this input. -/
theorem actualEquationsInMaximalIdeal (w : F.tripleIncidence G H)
    (t s : List (F.tripleIncidenceAmbientStalk G H w))
    (hker : RingHom.ker
      ((correspondenceSecondDiagonalInclusion X.hom Y.hom Z.hom W.hom ≫
        correspondenceFirstDiagonalInclusion X.hom Y.hom Z.hom W.hom).stalkMap
          (F.tripleIncidenceFourfoldInclusion G H w)).hom = Ideal.ofList (t ++ s)) :
    (∀ a ∈ t, a ∈ IsLocalRing.maximalIdeal (F.tripleIncidenceAmbientStalk G H w)) ∧
      (∀ a ∈ s, a ∈ IsLocalRing.maximalIdeal (F.tripleIncidenceAmbientStalk G H w)) :=
  combinedDiagonal_lists_mem_maximalIdeal X.hom Y.hom Z.hom W.hom
    (F.tripleIncidenceFourfoldInclusion G H w) t s hker

set_option backward.isDefEq.respectTransparency false in
/-- The original smooth middle equations cut out the full first-stage stalk
and index exactly its global source generics specializing to the chosen point. -/
theorem actualOriginalSupportIndices (w : F.tripleIncidence G H) :
    let p := F.tripleIncidenceSixfoldInclusion G H w
    ∃ t : List ((pullback Y.hom Y.hom).presheaf.stalk
      (correspondenceSixfoldFirstMiddlePair X.hom Y.hom Z.hom W.hom p)),
      let t' := t.map
        ((correspondenceSixfoldFirstMiddlePair X.hom Y.hom Z.hom W.hom).stalkMap p).hom
      let J := Ideal.ofList t' ⊔ Module.annihilator
        (F.tripleIncidenceAmbientStalk G H w) (F.tripleIncidenceSupportStalkModule G H w)
      Nonempty (((F.tripleIncidenceAmbientStalk G H w) ⧸ J) ≃+*
        (F.leftIntermediateSupportProduct G H).presheaf.stalk
          (F.tripleIncidenceToLeftSupportProduct G H w)) ∧
        Nonempty (J.minimalPrimes ≃
          {y : genericPoints (F.leftIntermediateSupportProduct G H) //
            y.1 ⤳ F.tripleIncidenceToLeftSupportProduct G H w}) := by
  dsimp only
  obtain ⟨t, _, _, _, _, _, ht, _⟩ := exists_common_regular_middle_diagonalLists
    X.hom Y.hom Z.hom W.hom (F.tripleIncidenceFourfoldInclusion G H w)
  exact ⟨t, ⟨F.tripleFirstStageSupportQuotientEquiv G H w _ ht⟩,
    ⟨F.tripleFirstStageSupportGenericEquiv G H w _ ht⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- On the actual smooth-site support, the reverse geometric index is the
literal contraction of its actual stalk-spectrum prime. -/
theorem actualSupportIndexReverseContraction (w : F.tripleIncidence G H)
    (t : List (F.tripleIncidenceAmbientStalk G H w))
    (ht : (correspondenceFirstDiagonalInclusion X.hom Y.hom Z.hom W.hom).ker.stalk
      (F.tripleIncidenceSixfoldInclusion G H w) = Ideal.ofList t)
    (y : {y : genericPoints (F.leftIntermediateSupportProduct G H) //
      y.1 ⤳ F.tripleIncidenceToLeftSupportProduct G H w}) :
    ((F.tripleFirstStageSupportGenericEquiv G H w t ht).symm y).1 =
      (((stalkGenericPointEquiv (F.leftIntermediateSupportProduct G H)
        (F.tripleIncidenceToLeftSupportProduct G H w)).symm y).1.asIdeal).comap
          (F.tripleFirstStageStalkMap G H w).hom :=
  F.tripleFirstStageSupportGenericEquiv_symm_val G H w t ht y

set_option backward.isDefEq.respectTransparency false in
/-- The geometrically indexed original-support sum computes canonical triple
Tor, retaining exactly the specialization condition required by the local
support ideal and without replacing any weight by an image-cycle coefficient. -/
theorem actualGeometricFixedSupportCoefficient
    (w : genericPoints (F.tripleIncidence G H))
    (t s : List (F.tripleIncidenceAmbientStalk G H w.val))
    (ht : (correspondenceFirstDiagonalInclusion X.hom Y.hom Z.hom W.hom).ker.stalk
      (F.tripleIncidenceSixfoldInclusion G H w.val) = Ideal.ofList t)
    (hr : IsRegular (F.tripleIncidenceAmbientStalk G H w.val) (t ++ s))
    (hker : RingHom.ker
      ((correspondenceSecondDiagonalInclusion X.hom Y.hom Z.hom W.hom ≫
        correspondenceFirstDiagonalInclusion X.hom Y.hom Z.hom W.hom).stalkMap
          (F.tripleIncidenceFourfoldInclusion G H w.val)).hom = Ideal.ofList (t ++ s)) :
    letI := isLocallyNoetherian_correspondenceSixfoldAmbient (S := Spec (.of k))
      X.hom Y.hom Z.hom W.hom
    letI := F.tripleTwoList_support_isArtinian (S := Spec (.of k)) G H w t s hker
    let M := F.tripleIncidenceSupportStalkModule G H w.val
    (∑ᶠ y : {y : genericPoints (F.leftIntermediateSupportProduct G H) //
      y.1 ⤳ F.tripleIncidenceToLeftSupportProduct G H w.val},
      let p := (F.tripleFirstStageSupportGenericEquiv G H w.val t ht).symm y
      Koszul.twoListGenericEuler M t p *
        chainEuler (Koszul.coefficientComplex
          (ModuleCat.of (F.tripleIncidenceAmbientStalk G H w.val)
            ((F.tripleIncidenceAmbientStalk G H w.val) ⧸ p.1)) s)
          (Koszul.fixedSupport_prime_finiteHomology s
            (Ideal.ofList t ⊔ Module.annihilator
              (F.tripleIncidenceAmbientStalk G H w.val) M) p.1 p.2.le)) =
      F.tripleIncidenceTorCoefficient (S := Spec (.of k)) G H w :=
  F.triple_geometric_fixedSupport_sum_eq_coefficient (S := Spec (.of k)) G H w t s ht hr hker

end Motivic.MotivicTest.TripleFixedSupportTorComparison
