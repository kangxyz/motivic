/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.TripleCommonRegularity
public import Motivic.AlgebraicGeometry.Correspondences.TripleIncidenceTor
public import Motivic.Algebra.Homology.KoszulTwoListOrderComparison

/-!
# The same original two-list total computes canonical triple Tor

The literal common middle lists form a jointly regular append by their actual
quotient regularity. The genuine coefficient tensor comparison, append
isomorphism, associator and signed tensor symmetry identify its Koszul complex
with the actual two-list total. Thus canonical triple categorical Tor and its
finite Euler coefficient agree with that total in both orders. No iterated
finite-correspondence pairing is identified with either total here.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits AlgebraicGeometry
open Motivic.LengthEuler

universe u

namespace Motivic.Koszul

variable {R : Type u} [CommRing R]

/-- The actual coefficient Koszul complex of an append is the tensor total
of the first Koszul complex with the second coefficient complex. -/
def coefficientAppendIso (M : ModuleCat R) (t s : List R) :
    coefficientComplex M (t ++ s) ≅
      HomologicalComplex.tensorObj (chainComplex t) (coefficientComplex M s) :=
  TorComparison.coefficientComplexTensorIso M (t ++ s) ≪≫
    whiskerRightIso (appendIso t s) ((ChainComplex.single₀ (ModuleCat R)).obj M) ≪≫
    (α_ (chainComplex t) (chainComplex s) ((ChainComplex.single₀ (ModuleCat R)).obj M)) ≪≫
    whiskerLeftIso (chainComplex t) (TorComparison.coefficientComplexTensorIso M s).symm

/-- The remaining-first two-list total is the same actual append complex,
with the Koszul signs accounted for by the proved signed tensor symmetry. -/
def twoListTotalAppendIso (M : ModuleCat R) (s t : List R) :
    HomologicalComplex.tensorObj (chainComplex s) (coefficientComplex M t) ≅
      coefficientComplex M (t ++ s) :=
  twoListOrderIso M s t ≪≫ (coefficientAppendIso M t s).symm

end Motivic.Koszul

namespace Motivic.FiniteCorrespondenceGenerator

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)
  [IsLocallyNoetherian S] [LocallyOfFiniteType f] [LocallyOfFiniteType i]
  [Flat f] [Smooth g] [IsSeparated g] [Smooth h] [IsSeparated h] [Flat i]

set_option backward.isDefEq.respectTransparency false in
/-- At a genuine generic triple point, the actual total of the same original
middle lists computes every canonical Tor degree and its full Euler coefficient.
All finite homology is derived from actual generic support. -/
theorem triple_common_total_coefficient (w : genericPoints (F.tripleIncidence G H)) :
    let p := F.tripleIncidenceSixfoldInclusion G H w.val
    ∀ (t : List ((pullback g g).presheaf.stalk
        (correspondenceSixfoldFirstMiddlePair f g h i p)))
      (s : List ((pullback h h).presheaf.stalk
        (correspondenceSixfoldSecondMiddlePair f g h i p))),
      RingTheory.Sequence.IsWeaklyRegular ((pullback g g).presheaf.stalk
        (correspondenceSixfoldFirstMiddlePair f g h i p)) t →
      RingTheory.Sequence.IsWeaklyRegular ((pullback h h).presheaf.stalk
        (correspondenceSixfoldSecondMiddlePair f g h i p)) s →
      (correspondenceFirstDiagonalInclusion f g h i).ker.stalk p =
        Ideal.ofList (t.map ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap p).hom) →
      (correspondenceSecondAmbientInclusion f g h i).ker.stalk p =
        Ideal.ofList (s.map ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap p).hom) →
      let t' := t.map ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap p).hom
      let s' := s.map ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap p).hom
      let K := HomologicalComplex.tensorObj (Koszul.chainComplex s')
        (Koszul.coefficientComplex (F.tripleIncidenceSupportStalkModule G H w.val) t')
      ∃ hK : FiniteHomology K,
        (∀ n : ℕ, Nonempty (F.tripleIncidenceTor G H w.val n ≅ K.homology n)) ∧
        F.tripleIncidenceTorCoefficient G H w = chainEuler K hK := by
  dsimp only
  intro t s ht hs hkt hks
  let p := F.tripleIncidenceSixfoldInclusion G H w.val
  let t' := t.map ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap p).hom
  let s' := s.map ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap p).hom
  let M := F.tripleIncidenceSupportStalkModule G H w.val
  obtain ⟨hr, hker⟩ := common_middle_diagonalLists_append_regular f g h i
    (F.tripleIncidenceFourfoldInclusion G H w.val) t s ht hs hkt hks
  let e := Koszul.twoListTotalAppendIso M s' t'
  have hA := F.tripleIncidenceKoszul_finiteHomology G H w (t' ++ s') hker
  have hK := hA.of_quasiIso e.inv
  refine ⟨hK, ?_, ?_⟩
  · intro n
    exact ⟨Intersection.torIsoHomology
      (correspondenceSecondDiagonalInclusion f g h i ≫
        correspondenceFirstDiagonalInclusion f g h i)
      (F.tripleIncidenceFourfoldInclusion G H w.val) (F.tripleSupportProductInclusion G H)
      ((F.tripleIncidenceToLeftSupportProduct G H ≫ F.leftIntermediateToTripleSupport G H) w.val)
      (Intersection.point_eq _ _ _ _ (F.tripleIncidence_sixfold_isPullback G H) w.val)
      (t' ++ s') hker hr n ≪≫
      (HomologicalComplex.homologyFunctor (ModuleCat (F.tripleIncidenceAmbientStalk G H w.val))
        (ComplexShape.down ℕ) n).mapIso e.symm⟩
  · exact (F.tripleIncidenceTorCoefficient_eq_chainEuler G H w (t' ++ s') hr hker).trans
      (homologyEuler_eq_of_quasiIso e.inv (fun n => (-1) ^ n) hA hK)

set_option backward.isDefEq.respectTransparency false in
/-- A constructed pair of original smooth middle lists computes the actual
canonical Tor in every degree and its finite Euler coefficient. -/
theorem exists_common_total_tor (w : genericPoints (F.tripleIncidence G H)) :
    let p := F.tripleIncidenceSixfoldInclusion G H w.val
    ∃ (t : List ((pullback g g).presheaf.stalk
        (correspondenceSixfoldFirstMiddlePair f g h i p)))
      (s : List ((pullback h h).presheaf.stalk
        (correspondenceSixfoldSecondMiddlePair f g h i p))),
      let t' := t.map ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap p).hom
      let s' := s.map ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap p).hom
      let K := HomologicalComplex.tensorObj (Koszul.chainComplex s')
        (Koszul.coefficientComplex (F.tripleIncidenceSupportStalkModule G H w.val) t')
      ∃ hK : FiniteHomology K,
        (∀ n : ℕ, Nonempty (F.tripleIncidenceTor G H w.val n ≅ K.homology n)) ∧
        F.tripleIncidenceTorCoefficient G H w = chainEuler K hK := by
  dsimp only
  obtain ⟨t, s, ht, hs, _, _, hkt, hks⟩ := exists_common_regular_middle_diagonalLists f g h i
    (F.tripleIncidenceFourfoldInclusion G H w.val)
  exact ⟨t, s, F.triple_common_total_coefficient G H w t s
    ht.toIsWeaklyRegular hs.toIsWeaklyRegular hkt hks⟩

set_option backward.isDefEq.respectTransparency false in
/-- The actual canonical triple coefficient agrees with the two genuine
list-order totals for one constructed pair of original middle lists. Only the
first append is proved regular; the second order uses the signed chain isomorphism. -/
theorem exists_common_twoList_total_coefficient (w : genericPoints (F.tripleIncidence G H)) :
    let p := F.tripleIncidenceSixfoldInclusion G H w.val
    ∃ (t : List ((pullback g g).presheaf.stalk
        (correspondenceSixfoldFirstMiddlePair f g h i p)))
      (s : List ((pullback h h).presheaf.stalk
        (correspondenceSixfoldSecondMiddlePair f g h i p))),
      let t' := t.map ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap p).hom
      let s' := s.map ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap p).hom
      let M := F.tripleIncidenceSupportStalkModule G H w.val
      let K := HomologicalComplex.tensorObj (Koszul.chainComplex s')
        (Koszul.coefficientComplex M t')
      let L := HomologicalComplex.tensorObj (Koszul.chainComplex t')
        (Koszul.coefficientComplex M s')
      ∃ (hK : FiniteHomology K) (hL : FiniteHomology L),
        F.tripleIncidenceTorCoefficient G H w = chainEuler K hK ∧
        F.tripleIncidenceTorCoefficient G H w = chainEuler L hL := by
  dsimp only
  obtain ⟨t, s, ht, hs, _, _, hkt, hks⟩ := exists_common_regular_middle_diagonalLists f g h i
    (F.tripleIncidenceFourfoldInclusion G H w.val)
  obtain ⟨hK, _, hE⟩ := F.triple_common_total_coefficient G H w t s
    ht.toIsWeaklyRegular hs.toIsWeaklyRegular hkt hks
  refine ⟨t, s, hK, Koszul.twoListOrder_finiteHomology _ _ _ hK, hE, ?_⟩
  exact hE.trans (Koszul.twoListOrder_chainEuler _ _ _ hK)

end Motivic.FiniteCorrespondenceGenerator
