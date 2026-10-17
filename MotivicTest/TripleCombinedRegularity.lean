/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.TripleCombinedRegularity
public import Motivic.AlgebraicGeometry.Intersection.GenericTor
public import Motivic.AlgebraicGeometry.SmoothSiteNoetherian

/-!
# Genuine combined-diagonal regularity on actual smooth-site triples

These consumers apply the constructed combined kernel to the original
exterior support in the six-factor ambient. The Tor/Koszul isomorphisms and
the vanishing bound are conclusions, with no supplied regularity or resolution.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingTheory.Sequence

universe u

namespace Motivic.MotivicTest.TripleCombinedRegularity

open Intersection

variable (k : Type u) [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

/-- The actual combined inclusion has regular stalk kernel on arbitrary smooth-site objects. -/
theorem actualCombinedKernel (q : correspondenceFourfoldProduct X.hom Y.hom Z.hom W.hom) :
    let d := correspondenceSecondDiagonalInclusion X.hom Y.hom Z.hom W.hom ≫
      correspondenceFirstDiagonalInclusion X.hom Y.hom Z.hom W.hom
    ∃ r : List (ambientStalk d q), IsRegular (ambientStalk d q) r ∧
      RingHom.ker (d.stalkMap q).hom = Ideal.ofList r :=
  exists_regular_kernel_correspondenceFourfoldDiagonal X.hom Y.hom Z.hom W.hom q

/-- The constructed regular combined kernel resolves the actual fourfold stalk
and computes total Tor with the original exterior coefficient support. -/
theorem actualTotalTorKoszul (w : F.tripleIncidence G H) :
    let a := F.tripleIncidenceFourfoldInclusion G H
    let b := F.tripleIncidenceToLeftSupportProduct G H ≫ F.leftIntermediateToTripleSupport G H
    let d := correspondenceSecondDiagonalInclusion X.hom Y.hom Z.hom W.hom ≫
      correspondenceFirstDiagonalInclusion X.hom Y.hom Z.hom W.hom
    let j := F.tripleSupportProductInclusion G H
    let hp := point_eq a b d j (F.tripleIncidence_sixfold_isPullback G H) w
    let M := coefficientStalkModule d (a w) j (b w) hp
    ∃ r : List (ambientStalk d (a w)), IsRegular (ambientStalk d (a w)) r ∧
      RingHom.ker (d.stalkMap (a w)).hom = Ideal.ofList r ∧
      ∀ n : ℕ, Nonempty
        ((((Tor (ModuleCat (ambientStalk d (a w))) n).obj M).obj
          (sourceStalkModule d (a w))) ≅ (Koszul.coefficientComplex M r).homology n) := by
  dsimp only
  obtain ⟨r, hr, hker⟩ := actualCombinedKernel k (F.tripleIncidenceFourfoldInclusion G H w)
  exact ⟨r, hr, hker, fun n => ⟨torIsoHomology _ _ _ _ _ r hker hr n⟩⟩

/-- A genuine finite regular resolution bounds total categorical Tor at every
actual triple point, without coefficient-flatness or genericity hypotheses. -/
theorem actualTotalTorBound (w : F.tripleIncidence G H) :
    let a := F.tripleIncidenceFourfoldInclusion G H
    let b := F.tripleIncidenceToLeftSupportProduct G H ≫ F.leftIntermediateToTripleSupport G H
    let d := correspondenceSecondDiagonalInclusion X.hom Y.hom Z.hom W.hom ≫
      correspondenceFirstDiagonalInclusion X.hom Y.hom Z.hom W.hom
    let j := F.tripleSupportProductInclusion G H
    let hp := point_eq a b d j (F.tripleIncidence_sixfold_isPullback G H) w
    ∃ N : ℕ, ∀ n : ℕ, N < n → IsZero
      (((Tor (ModuleCat (ambientStalk d (a w))) n).obj
        (coefficientStalkModule d (a w) j (b w) hp)).obj (sourceStalkModule d (a w))) := by
  dsimp only
  obtain ⟨r, hr, hker⟩ := actualCombinedKernel k (F.tripleIncidenceFourfoldInclusion G H w)
  exact ⟨r.length, fun n hn => isZero_tor_above_length _ _ _ _ _ r hker hr n hn⟩

end Motivic.MotivicTest.TripleCombinedRegularity
