/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.TripleFirstStageSupportIndex
public import Motivic.AlgebraicGeometry.Correspondences.TripleTwoListTorComparison

/-!
# Actual fixed-support replacement sums compute canonical triple Tor

The genuine combined kernel cuts out the full generic incidence support with
the original exterior coefficient annihilator. Its quotient is therefore
Artinian, and its literal equations lie in the ambient maximal ideal. These
proved inputs apply the existing fixed-support replacement theorem to the
actual two-list total. Its minimal-prime sum equals the canonical triple Tor
coefficient. No summand is identified here with an original pair-incidence or
finite-image cycle coefficient.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingTheory.Sequence
open Motivic.LengthEuler

universe u

namespace Motivic

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)

/-- Every equation in a presentation of the actual combined kernel lies in
the ambient maximal ideal, because the final fourfold stalk is nonzero. -/
theorem combinedDiagonal_lists_mem_maximalIdeal
    (q : correspondenceFourfoldProduct f g h i)
    (t s : List (Intersection.ambientStalk
      (correspondenceSecondDiagonalInclusion f g h i ≫
        correspondenceFirstDiagonalInclusion f g h i) q))
    (hker : RingHom.ker
      ((correspondenceSecondDiagonalInclusion f g h i ≫
        correspondenceFirstDiagonalInclusion f g h i).stalkMap q).hom =
      Ideal.ofList (t ++ s)) :
    (∀ a ∈ t, a ∈ IsLocalRing.maximalIdeal (Intersection.ambientStalk
      (correspondenceSecondDiagonalInclusion f g h i ≫
        correspondenceFirstDiagonalInclusion f g h i) q)) ∧
    (∀ a ∈ s, a ∈ IsLocalRing.maximalIdeal (Intersection.ambientStalk
      (correspondenceSecondDiagonalInclusion f g h i ≫
        correspondenceFirstDiagonalInclusion f g h i) q)) := by
  have hI : Ideal.ofList (t ++ s) ≤ IsLocalRing.maximalIdeal _ := by
    rw [← hker]
    exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
  constructor
  · intro a ha
    exact hI (Ideal.subset_span (List.mem_append.mpr (Or.inl ha)))
  · intro a ha
    exact hI (Ideal.subset_span (List.mem_append.mpr (Or.inr ha)))

namespace FiniteCorrespondenceGenerator

variable {f g h i}
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)
  [IsLocallyNoetherian S] [LocallyOfFiniteType f] [LocallyOfFiniteType i]
  [Flat f] [Smooth g] [IsSeparated g] [Smooth h] [IsSeparated h] [Flat i]

omit [LocallyOfFiniteType i] [Flat f] [Flat i] [Smooth g] [Smooth h] in
/-- The full actual generic support makes the two-list coefficient-support
quotient Artinian, without assuming that the ambient local ring is Artinian. -/
theorem tripleTwoList_support_isArtinian
    (w : genericPoints (F.tripleIncidence G H))
    (t s : List (F.tripleIncidenceAmbientStalk G H w.val))
    (hker : RingHom.ker
      ((correspondenceSecondDiagonalInclusion f g h i ≫
        correspondenceFirstDiagonalInclusion f g h i).stalkMap
          (F.tripleIncidenceFourfoldInclusion G H w.val)).hom = Ideal.ofList (t ++ s)) :
    IsArtinianRing ((F.tripleIncidenceAmbientStalk G H w.val) ⧸
      (Ideal.ofList s ⊔ (Ideal.ofList t ⊔
        Module.annihilator (F.tripleIncidenceAmbientStalk G H w.val)
          (F.tripleIncidenceSupportStalkModule G H w.val)))) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := LocallyOfFiniteType.isLocallyNoetherian (F.tripleIncidenceSource G H)
  rw [sup_left_comm, ← sup_assoc, ← Ideal.ofList_append, ← hker]
  rw [Intersection.coefficientStalkModule_annihilator]
  exact Intersection.stalk_sum_quotient_isArtinian
    (F.tripleIncidenceFourfoldInclusion G H)
    (F.tripleIncidenceToLeftSupportProduct G H ≫ F.leftIntermediateToTripleSupport G H)
    (correspondenceSecondDiagonalInclusion f g h i ≫ correspondenceFirstDiagonalInclusion f g h i)
    (F.tripleSupportProductInclusion G H) (F.tripleIncidence_sixfold_isPullback G H)
    w.val w.property

set_option backward.isDefEq.respectTransparency false in
/-- The actual fixed-support minimal-prime replacement sum equals canonical
triple Tor for a genuine combined regular presentation, with its support and
maximal-ideal hypotheses derived from the original geometry. -/
theorem triple_fixedSupport_sum_eq_coefficient
    (w : genericPoints (F.tripleIncidence G H))
    (t s : List (F.tripleIncidenceAmbientStalk G H w.val))
    (hr : IsRegular (F.tripleIncidenceAmbientStalk G H w.val) (t ++ s))
    (hker : RingHom.ker
      ((correspondenceSecondDiagonalInclusion f g h i ≫
        correspondenceFirstDiagonalInclusion f g h i).stalkMap
          (F.tripleIncidenceFourfoldInclusion G H w.val)).hom = Ideal.ofList (t ++ s)) :
    letI := isLocallyNoetherian_correspondenceSixfoldAmbient f g h i
    letI := F.tripleTwoList_support_isArtinian G H w t s hker
    Koszul.twoListFixedSupportSum (F.tripleIncidenceSupportStalkModule G H w.val) s t =
      F.tripleIncidenceTorCoefficient G H w := by
  let := isLocallyNoetherian_correspondenceSixfoldAmbient f g h i
  let := F.tripleTwoList_support_isArtinian G H w t s hker
  let M := F.tripleIncidenceSupportStalkModule G H w.val
  have hs := (combinedDiagonal_lists_mem_maximalIdeal f g h i
    (F.tripleIncidenceFourfoldInclusion G H w.val) t s hker).2
  obtain ⟨hK, hE⟩ := Koszul.twoList_chainEuler_replacement M s t hs
  let e := Koszul.twoListTotalAppendIso M s t
  have hA := F.tripleIncidenceKoszul_finiteHomology G H w (t ++ s) hker
  have hc : F.tripleIncidenceTorCoefficient G H w =
      chainEuler (HomologicalComplex.tensorObj (Koszul.chainComplex s)
        (Koszul.coefficientComplex M t)) hK :=
    (F.tripleIncidenceTorCoefficient_eq_chainEuler G H w (t ++ s) hr hker).trans
      (homologyEuler_eq_of_quasiIso e.hom (fun n => (-1) ^ n) hK hA).symm
  exact hE.symm.trans hc.symm

set_option backward.isDefEq.respectTransparency false in
omit [Flat f] [Flat i] in
/-- The actual fixed-support sum is indexed by original first-stage source
components specializing to the chosen point, using their literal contracted
stalk primes. This does not identify the weights with finite-image coefficients. -/
theorem triple_fixedSupport_sum_reindex
    (w : genericPoints (F.tripleIncidence G H))
    (t s : List (F.tripleIncidenceAmbientStalk G H w.val))
    (ht : (correspondenceFirstDiagonalInclusion f g h i).ker.stalk
      (F.tripleIncidenceSixfoldInclusion G H w.val) = Ideal.ofList t)
    (hker : RingHom.ker
      ((correspondenceSecondDiagonalInclusion f g h i ≫
        correspondenceFirstDiagonalInclusion f g h i).stalkMap
          (F.tripleIncidenceFourfoldInclusion G H w.val)).hom = Ideal.ofList (t ++ s)) :
    letI := isLocallyNoetherian_correspondenceSixfoldAmbient f g h i
    letI := F.tripleTwoList_support_isArtinian G H w t s hker
    let M := F.tripleIncidenceSupportStalkModule G H w.val
    Koszul.twoListFixedSupportSum M s t =
      ∑ᶠ y : {y : genericPoints (F.leftIntermediateSupportProduct G H) //
        y.1 ⤳ F.tripleIncidenceToLeftSupportProduct G H w.val},
        let p := (F.tripleFirstStageSupportGenericEquiv G H w.val t ht).symm y
        Koszul.twoListGenericEuler M t p *
          chainEuler (Koszul.coefficientComplex
            (ModuleCat.of (F.tripleIncidenceAmbientStalk G H w.val)
              ((F.tripleIncidenceAmbientStalk G H w.val) ⧸ p.1)) s)
            (Koszul.fixedSupport_prime_finiteHomology s
              (Ideal.ofList t ⊔ Module.annihilator
                (F.tripleIncidenceAmbientStalk G H w.val) M) p.1 p.2.le) := by
  dsimp only
  let := isLocallyNoetherian_correspondenceSixfoldAmbient f g h i
  let := F.tripleTwoList_support_isArtinian G H w t s hker
  exact F.tripleFirstStageSupport_finsum G H w.val t ht _

set_option backward.isDefEq.respectTransparency false in
/-- The geometrically indexed original-support sum computes canonical triple
Tor, retaining exactly the specialization condition required by the local
support ideal and without replacing any weight by an image-cycle coefficient. -/
theorem triple_geometric_fixedSupport_sum_eq_coefficient
    (w : genericPoints (F.tripleIncidence G H))
    (t s : List (F.tripleIncidenceAmbientStalk G H w.val))
    (ht : (correspondenceFirstDiagonalInclusion f g h i).ker.stalk
      (F.tripleIncidenceSixfoldInclusion G H w.val) = Ideal.ofList t)
    (hr : IsRegular (F.tripleIncidenceAmbientStalk G H w.val) (t ++ s))
    (hker : RingHom.ker
      ((correspondenceSecondDiagonalInclusion f g h i ≫
        correspondenceFirstDiagonalInclusion f g h i).stalkMap
          (F.tripleIncidenceFourfoldInclusion G H w.val)).hom = Ideal.ofList (t ++ s)) :
    letI := isLocallyNoetherian_correspondenceSixfoldAmbient f g h i
    letI := F.tripleTwoList_support_isArtinian G H w t s hker
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
      F.tripleIncidenceTorCoefficient G H w := by
  dsimp only
  let := isLocallyNoetherian_correspondenceSixfoldAmbient f g h i
  let := F.tripleTwoList_support_isArtinian G H w t s hker
  exact (F.triple_fixedSupport_sum_reindex G H w t s ht hker).symm.trans
    (F.triple_fixedSupport_sum_eq_coefficient G H w t s hr hker)

set_option backward.isDefEq.respectTransparency false in
/-- Both literal fixed-support replacement sums compute the same canonical
coefficient. The reversed order follows by genuine signed total comparison. -/
theorem triple_both_fixedSupport_sums_eq_coefficient
    (w : genericPoints (F.tripleIncidence G H))
    (t s : List (F.tripleIncidenceAmbientStalk G H w.val))
    (hr : IsRegular (F.tripleIncidenceAmbientStalk G H w.val) (t ++ s))
    (hker : RingHom.ker
      ((correspondenceSecondDiagonalInclusion f g h i ≫
        correspondenceFirstDiagonalInclusion f g h i).stalkMap
          (F.tripleIncidenceFourfoldInclusion G H w.val)).hom = Ideal.ofList (t ++ s)) :
    letI := isLocallyNoetherian_correspondenceSixfoldAmbient f g h i
    letI := F.tripleTwoList_support_isArtinian G H w t s hker
    let M := F.tripleIncidenceSupportStalkModule G H w.val
    Koszul.twoListFixedSupportSum M s t = F.tripleIncidenceTorCoefficient G H w ∧
      letI := Koszul.twoList_swappedArtinian M s t
      Koszul.twoListFixedSupportSum M t s = F.tripleIncidenceTorCoefficient G H w := by
  dsimp only
  let := isLocallyNoetherian_correspondenceSixfoldAmbient f g h i
  let := F.tripleTwoList_support_isArtinian G H w t s hker
  let M := F.tripleIncidenceSupportStalkModule G H w.val
  have hm := combinedDiagonal_lists_mem_maximalIdeal f g h i
    (F.tripleIncidenceFourfoldInclusion G H w.val) t s hker
  have hc := F.triple_fixedSupport_sum_eq_coefficient G H w t s hr hker
  refine ⟨hc, ?_⟩
  exact (Koszul.twoListFixedSupportSum_order M s t hm.2 hm.1).symm.trans hc

set_option backward.isDefEq.respectTransparency false in
/-- Original smooth middle lists construct both genuine fixed-support
minimal-prime sums equal to canonical triple Tor, without an input support or
regular-presentation witness. -/
theorem exists_common_fixedSupport_sums (w : genericPoints (F.tripleIncidence G H)) :
    letI := isLocallyNoetherian_correspondenceSixfoldAmbient f g h i
    let p := F.tripleIncidenceSixfoldInclusion G H w.val
    ∃ (t : List ((pullback g g).presheaf.stalk
        (correspondenceSixfoldFirstMiddlePair f g h i p)))
      (s : List ((pullback h h).presheaf.stalk
        (correspondenceSixfoldSecondMiddlePair f g h i p))),
      let t' := t.map ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap p).hom
      let s' := s.map ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap p).hom
      ∃ hker : RingHom.ker
        ((correspondenceSecondDiagonalInclusion f g h i ≫
          correspondenceFirstDiagonalInclusion f g h i).stalkMap
            (F.tripleIncidenceFourfoldInclusion G H w.val)).hom = Ideal.ofList (t' ++ s'),
        letI := F.tripleTwoList_support_isArtinian G H w t' s' hker
        let M := F.tripleIncidenceSupportStalkModule G H w.val
        Koszul.twoListFixedSupportSum M s' t' = F.tripleIncidenceTorCoefficient G H w ∧
          letI := Koszul.twoList_swappedArtinian M s' t'
          Koszul.twoListFixedSupportSum M t' s' = F.tripleIncidenceTorCoefficient G H w := by
  dsimp only
  let := isLocallyNoetherian_correspondenceSixfoldAmbient f g h i
  obtain ⟨t, s, ht, hs, _, _, hkt, hks⟩ := exists_common_regular_middle_diagonalLists f g h i
    (F.tripleIncidenceFourfoldInclusion G H w.val)
  obtain ⟨hr, hker⟩ := common_middle_diagonalLists_append_regular f g h i
    (F.tripleIncidenceFourfoldInclusion G H w.val) t s
      ht.toIsWeaklyRegular hs.toIsWeaklyRegular hkt hks
  exact ⟨t, s, hker, F.triple_both_fixedSupport_sums_eq_coefficient G H w _ _ hr hker⟩

end FiniteCorrespondenceGenerator

end Motivic
