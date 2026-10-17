/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.TripleTwoListTorComparison
public import Motivic.AlgebraicGeometry.SmoothSiteNoetherian

/-!
# Actual common-list comparison with canonical triple total Tor

These smooth-site consumers construct the original common middle lists and
their literal combined regular kernel, then compare the actual two-list
complexes with the already canonical triple-incidence coefficient.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingTheory.Sequence
open Motivic.LengthEuler

universe u

namespace Motivic.MotivicTest.TripleCommonTorComparison

variable (k : Type u) [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

set_option backward.isDefEq.respectTransparency false in
/-- The same original two middle lists give a genuinely regular literal append
in the original six-factor ambient at every actual triple-incidence point. -/
theorem actualLiteralCombinedKernel (w : F.tripleIncidence G H) :
    let p := F.tripleIncidenceSixfoldInclusion G H w
    ∃ (t : List ((pullback Y.hom Y.hom).presheaf.stalk
        (correspondenceSixfoldFirstMiddlePair X.hom Y.hom Z.hom W.hom p)))
      (s : List ((pullback Z.hom Z.hom).presheaf.stalk
        (correspondenceSixfoldSecondMiddlePair X.hom Y.hom Z.hom W.hom p))),
      let r :=
        t.map ((correspondenceSixfoldFirstMiddlePair X.hom Y.hom Z.hom W.hom).stalkMap p).hom ++
        s.map ((correspondenceSixfoldSecondMiddlePair X.hom Y.hom Z.hom W.hom).stalkMap p).hom
      IsRegular
        ((correspondenceSixfoldAmbient X.hom Y.hom Z.hom W.hom).presheaf.stalk p) r ∧
        RingHom.ker
          ((correspondenceSecondDiagonalInclusion X.hom Y.hom Z.hom W.hom ≫
            correspondenceFirstDiagonalInclusion X.hom Y.hom Z.hom W.hom).stalkMap
              (F.tripleIncidenceFourfoldInclusion G H w)).hom = Ideal.ofList r := by
  dsimp only
  obtain ⟨t, s, ht, hs, _, _, hkt, hks⟩ := exists_common_regular_middle_diagonalLists
    X.hom Y.hom Z.hom W.hom (F.tripleIncidenceFourfoldInclusion G H w)
  exact ⟨t, s, common_middle_diagonalLists_append_regular X.hom Y.hom Z.hom W.hom
    (F.tripleIncidenceFourfoldInclusion G H w) t s
      ht.toIsWeaklyRegular hs.toIsWeaklyRegular hkt hks⟩

set_option backward.isDefEq.respectTransparency false in
/-- The original common two-list total computes all canonical Tor degrees at
an actual generic triple point, with finite homology proved by the geometry. -/
theorem actualCommonTotalTor (w : genericPoints (F.tripleIncidence G H)) :
    let p := F.tripleIncidenceSixfoldInclusion G H w.val
    ∃ (t : List ((pullback Y.hom Y.hom).presheaf.stalk
        (correspondenceSixfoldFirstMiddlePair X.hom Y.hom Z.hom W.hom p)))
      (s : List ((pullback Z.hom Z.hom).presheaf.stalk
        (correspondenceSixfoldSecondMiddlePair X.hom Y.hom Z.hom W.hom p))),
      let t' := t.map
        ((correspondenceSixfoldFirstMiddlePair X.hom Y.hom Z.hom W.hom).stalkMap p).hom
      let s' := s.map
        ((correspondenceSixfoldSecondMiddlePair X.hom Y.hom Z.hom W.hom).stalkMap p).hom
      let K := HomologicalComplex.tensorObj (Koszul.chainComplex s')
        (Koszul.coefficientComplex (F.tripleIncidenceSupportStalkModule G H w.val) t')
      ∃ hK : FiniteHomology K,
        (∀ n : ℕ, Nonempty (F.tripleIncidenceTor G H w.val n ≅ K.homology n)) ∧
        F.tripleIncidenceTorCoefficient (S := Spec (.of k)) G H w = chainEuler K hK :=
  F.exists_common_total_tor (S := Spec (.of k)) G H w

set_option backward.isDefEq.respectTransparency false in
/-- Both actual list-order total Euler coefficients equal the same canonical
triple coefficient; no iterated finite-correspondence pairing is assumed. -/
theorem actualBothTotalOrders (w : genericPoints (F.tripleIncidence G H)) :
    let p := F.tripleIncidenceSixfoldInclusion G H w.val
    ∃ (t : List ((pullback Y.hom Y.hom).presheaf.stalk
        (correspondenceSixfoldFirstMiddlePair X.hom Y.hom Z.hom W.hom p)))
      (s : List ((pullback Z.hom Z.hom).presheaf.stalk
        (correspondenceSixfoldSecondMiddlePair X.hom Y.hom Z.hom W.hom p))),
      let t' := t.map
        ((correspondenceSixfoldFirstMiddlePair X.hom Y.hom Z.hom W.hom).stalkMap p).hom
      let s' := s.map
        ((correspondenceSixfoldSecondMiddlePair X.hom Y.hom Z.hom W.hom).stalkMap p).hom
      let M := F.tripleIncidenceSupportStalkModule G H w.val
      let K := HomologicalComplex.tensorObj (Koszul.chainComplex s')
        (Koszul.coefficientComplex M t')
      let L := HomologicalComplex.tensorObj (Koszul.chainComplex t')
        (Koszul.coefficientComplex M s')
      ∃ (hK : FiniteHomology K) (hL : FiniteHomology L),
        F.tripleIncidenceTorCoefficient (S := Spec (.of k)) G H w = chainEuler K hK ∧
        F.tripleIncidenceTorCoefficient (S := Spec (.of k)) G H w = chainEuler L hL :=
  F.exists_common_twoList_total_coefficient (S := Spec (.of k)) G H w

end Motivic.MotivicTest.TripleCommonTorComparison
