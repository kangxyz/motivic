/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.TripleDiagonalRegularity
public import Motivic.AlgebraicGeometry.Correspondences.IntermediateDiagonalLists
public import Motivic.AlgebraicGeometry.Intersection.GenericTor

/-!
# Actual first-stage Tor from genuine regular middle equations

The first-stage Tor/Koszul comparison below constructs its regular kernel
list. At an actual full triple point, the original common lists remain
regular in the same ambient stalk and the original remaining list satisfies
the genuine finite-image scalar square. No Tor comparison is a hypothesis.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingTheory.Sequence

universe u

namespace Motivic.MotivicTest.TripleDiagonalRegularity

open Intersection

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)

/-- Actual first-stage Tor uses a constructed regular list and the genuine
exterior support coefficient, in the original coefficient/source order. -/
theorem actualFirstStageTor [Flat f] [Smooth g] [IsSeparated g] [Flat h] [Flat i]
    (w : F.leftIntermediateSupportProduct G H) :
    let a := F.leftIntermediateSupportInclusion G H
    let b := F.leftIntermediateToTripleSupport G H
    let d := correspondenceFirstDiagonalInclusion f g h i
    let j := F.tripleSupportProductInclusion G H
    let hp := point_eq a b d j (F.leftIntermediate_ambient_isPullback G H) w
    let M := coefficientStalkModule d (a w) j (b w) hp
    ∃ t : List (ambientStalk d (a w)),
      IsRegular (ambientStalk d (a w)) t ∧
      RingHom.ker (d.stalkMap (a w)).hom = Ideal.ofList t ∧
      ∀ n : ℕ, Nonempty
        ((((Tor (ModuleCat (ambientStalk d (a w))) n).obj M).obj (sourceStalkModule d (a w))) ≅
          (Koszul.coefficientComplex M t).homology n) := by
  dsimp only
  obtain ⟨t, ht, hker⟩ := exists_regular_kernel_correspondenceFirstDiagonal f g h i
    (F.leftIntermediateSupportInclusion G H w)
  refine ⟨t, ht, hker, fun n => ⟨?_⟩⟩
  exact torIsoHomology _ _ _ _ _ t hker ht n

/-- The actual higher first-stage Tor vanishes above the length of a
constructed regular diagonal list, at every genuine first-stage point. -/
theorem actualFirstStageTorBound [Flat f] [Smooth g] [IsSeparated g] [Flat h] [Flat i]
    (w : F.leftIntermediateSupportProduct G H) :
    let a := F.leftIntermediateSupportInclusion G H
    let b := F.leftIntermediateToTripleSupport G H
    let d := correspondenceFirstDiagonalInclusion f g h i
    let j := F.tripleSupportProductInclusion G H
    let hp := point_eq a b d j (F.leftIntermediate_ambient_isPullback G H) w
    ∃ N : ℕ, ∀ n : ℕ, N < n → IsZero
      (((Tor (ModuleCat (ambientStalk d (a w))) n).obj
        (coefficientStalkModule d (a w) j (b w) hp)).obj (sourceStalkModule d (a w))) := by
  dsimp only
  obtain ⟨t, ht, hker⟩ := exists_regular_kernel_correspondenceFirstDiagonal f g h i
    (F.leftIntermediateSupportInclusion G H w)
  exact ⟨t.length, fun n hn => isZero_tor_above_length _ _ _ _ _ t hker ht n hn⟩

/-- At each actual triple point, both original common lists have regular
literal ambient images, and the remaining list follows the proved finite-image square. -/
theorem actualTripleCommonRegularLists [Flat f] [Smooth g] [IsSeparated g]
    [Smooth h] [IsSeparated h] [Flat i] (w : F.tripleIncidence G H) :
    let p := F.tripleIncidenceSixfoldInclusion G H w
    ∃ (t : List ((pullback g g).presheaf.stalk
        (correspondenceSixfoldFirstMiddlePair f g h i p)))
      (s : List ((pullback h h).presheaf.stalk
        (correspondenceSixfoldSecondMiddlePair f g h i p))),
      IsRegular ((correspondenceSixfoldAmbient f g h i).presheaf.stalk p)
        (t.map ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap p).hom) ∧
      IsRegular ((correspondenceSixfoldAmbient f g h i).presheaf.stalk p)
        (s.map ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap p).hom) ∧
      let u := F.tripleIncidenceToLeftSupportProduct G H w
      let s' := s.map (F.tripleRemainingMiddleStalkIso G H w).hom.hom
      (s'.map (F.leftImageMiddleStalkMap G H u).hom).map
          ((F.leftIntermediateImageMap G H).stalkMap u).hom =
        (s'.map (F.leftAmbientMiddleStalkMap G H u).hom).map
          ((F.leftIntermediateAmbientInclusion G H).stalkMap u).hom := by
  obtain ⟨t, s, _, _, ht, hs, _, _⟩ := exists_common_regular_middle_diagonalLists f g h i
    (F.tripleIncidenceFourfoldInclusion G H w)
  exact ⟨t, s, ht, hs, F.leftRemainingList_square G H _ _⟩

end Motivic.MotivicTest.TripleDiagonalRegularity
