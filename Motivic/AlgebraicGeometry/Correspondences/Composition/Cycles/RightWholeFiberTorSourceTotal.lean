/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.RightWholeFiberTorRemainingOuterSum
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.WholeFiberTorSourceTotal
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Associativity.TwoListTorComparison
public import Motivic.Aglib.Algebra.Homology.Koszul.HyperhomologyBounded
public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.RingEquiv

/-!
# The actual right fixed-list source outer sum computes canonical triple Tor

The same originally chosen remaining Y list is transported to every genuine
triple-incidence lift. Both the ambient and exterior-support point congruences
are retained in the actual coefficient scalar square. The genuine second
diagonal supported Tor is compared with the actual Z-list Koszul homology.
The actual bounded hyperhomology Euler theorem then attaches each original
source outer sum to canonical triple Tor, retaining the original finite fiber
and its residue weights. The accepted signed two-list chain isomorphism
changes total order; reversed append regularity is never assumed. Cycle
replacement and correspondence associativity remain separate.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingTheory.Sequence

universe u

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Products

private theorem alignedStalkMap_point_square {P Q : Scheme.{u}} (q : P ⟶ Q)
    (x x' : P) (e : x = x') (z z' : Q) (ez : z = z') (hz : z' = q x) :
    (Q.presheaf.stalkCongr (.of_eq ez)).hom ≫ Graph.alignedStalkMap q x z' hz ≫
        (P.presheaf.stalkCongr (.of_eq e)).hom =
      Graph.alignedStalkMap q x' z (ez.trans (hz.trans (congrArg q e))) := by
  subst x'
  subst z'
  simp

private theorem rightAlignedStalkMap_two_points_square {P Q : Scheme.{u}} (q : P ⟶ Q)
    (x x' : P) (ex : x = x') (z z' : Q) (ez : z = z')
    (hz : z = q x) (hz' : z' = q x') :
    (Q.presheaf.stalkCongr (.of_eq ez)).hom ≫ Graph.alignedStalkMap q x' z' hz' =
      Graph.alignedStalkMap q x z hz ≫ (P.presheaf.stalkCongr (.of_eq ex)).hom := by
  subst x'
  subst z'
  simp

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)
  (z : F.rightIntermediateImageProduct G H) (w : F.tripleIncidence G H)
  (hw : F.rightIntermediateImageMap G H (F.tripleIncidenceToRightSupportProduct G H w) = z)

include hw in
/-- The fixed image middle point equals the actual common six-factor middle point. -/
theorem rightFirstStageFiberTripleMiddlePoint :
    F.rightImageMiddlePair G H z =
      correspondenceSixfoldFirstMiddlePair f g h i (F.tripleIncidenceSixfoldInclusion G H w) :=
  (F.rightFiberMiddlePoint G H z ⟨_, hw⟩).trans (F.tripleRightRemainingMiddlePoint G H w)

/-- Only the actual equality of original middle points transports the common list. -/
def rightFirstStageFiberTripleMiddleStalkIso :
    (pullback g g).presheaf.stalk (F.rightImageMiddlePair G H z) ≅
      (pullback g g).presheaf.stalk
        (correspondenceSixfoldFirstMiddlePair f g h i (F.tripleIncidenceSixfoldInclusion G H w)) :=
  (pullback g g).presheaf.stalkCongr (.of_eq (F.rightFirstStageFiberTripleMiddlePoint G H z w hw))

/-- The first original middle list at a source lift is the SAME target-chosen list. -/
def rightFirstStageFiberTripleMiddleList
    (s : List ((pullback g g).presheaf.stalk (F.rightImageMiddlePair G H z))) :=
  s.map (F.rightFirstStageFiberTripleMiddleStalkIso G H z w hw).hom.hom

/-- The regularity witness of the fixed smooth target list survives its actual point transport. -/
theorem rightFirstStageFiberTripleMiddleList_isRegular
    (s : List ((pullback g g).presheaf.stalk (F.rightImageMiddlePair G H z)))
    (hs : IsRegular ((pullback g g).presheaf.stalk (F.rightImageMiddlePair G H z)) s) :
    IsRegular ((pullback g g).presheaf.stalk
      (correspondenceSixfoldFirstMiddlePair f g h i (F.tripleIncidenceSixfoldInclusion G H w)))
      (F.rightFirstStageFiberTripleMiddleList G H z w hw s) :=
  stalkCongr_regular (F.rightFirstStageFiberTripleMiddlePoint G H z w hw) s hs

/-- The same target list retains its literal original diagonal-kernel presentation. -/
theorem rightFirstStageFiberTripleMiddleList_kernel
    (s : List ((pullback g g).presheaf.stalk (F.rightImageMiddlePair G H z)))
    (hs : (pullback.diagonal g).ker.stalk (F.rightImageMiddlePair G H z) = Ideal.ofList s) :
    (pullback.diagonal g).ker.stalk
        (correspondenceSixfoldFirstMiddlePair f g h i (F.tripleIncidenceSixfoldInclusion G H w)) =
      Ideal.ofList (F.rightFirstStageFiberTripleMiddleList G H z w hw s) :=
  stalkCongr_kernel (pullback.diagonal g).ker
    (F.rightFirstStageFiberTripleMiddlePoint G H z w hw) s hs

omit z hw in
/-- The two ambient descriptions give literally equal original points. -/
theorem rightFirstStageTripleAmbientPoint :
    F.rightIntermediateAmbientInclusion G H (F.tripleIncidenceToRightSupportProduct G H w) =
      F.tripleIncidenceSixfoldInclusion G H w :=
  congrArg (fun a => a w) (F.tripleToRightSupport_ambient G H)

omit z hw in
/-- The first-stage and canonical triple ambient stalks differ only by
their actual point equality. -/
def rightFirstStageTripleAmbientStalkIso :
    (correspondenceSixfoldAmbient f g h i).presheaf.stalk
        (F.rightIntermediateAmbientInclusion G H (F.tripleIncidenceToRightSupportProduct G H w)) ≅
      F.tripleIncidenceAmbientStalk G H w :=
  (correspondenceSixfoldAmbient f g h i).presheaf.stalkCongr
    (.of_eq (F.rightFirstStageTripleAmbientPoint G H w))

/-- The literal middle-to-ambient square preserves the fixed target list
before any Tor comparison. -/
theorem rightFirstStageFiberTripleMiddleStalk_square :
    (F.rightFiberMiddleStalkIso G H z ⟨_, hw⟩).hom ≫
        F.rightAmbientMiddleStalkMap G H (F.tripleIncidenceToRightSupportProduct G H w) ≫
        (F.rightFirstStageTripleAmbientStalkIso G H w).hom =
      (F.rightFirstStageFiberTripleMiddleStalkIso G H z w hw).hom ≫
        (correspondenceSixfoldFirstMiddlePair f g h i).stalkMap
          (F.tripleIncidenceSixfoldInclusion G H w) := by
  simpa only [rightFiberMiddleStalkIso, rightAmbientMiddleStalkMap,
    rightFirstStageTripleAmbientStalkIso, rightFirstStageFiberTripleMiddleStalkIso,
    Graph.alignedStalkMap] using
    (alignedStalkMap_point_square (correspondenceSixfoldFirstMiddlePair f g h i)
      (F.rightIntermediateAmbientInclusion G H (F.tripleIncidenceToRightSupportProduct G H w))
      (F.tripleIncidenceSixfoldInclusion G H w) (F.rightFirstStageTripleAmbientPoint G H w)
      (F.rightImageMiddlePair G H z)
      (F.rightSupportMiddlePair G H (F.tripleIncidenceToRightSupportProduct G H w))
      (F.rightFiberMiddlePoint G H z ⟨_, hw⟩)
      (congrArg (fun a => a (F.tripleIncidenceToRightSupportProduct G H w))
        (F.rightIntermediateAmbientInclusion_middlePair G H)).symm)


/-- The actual ambient image of the fixed list agrees with the canonical two-list image. -/
theorem rightFirstStageFiberTripleMiddleList_ambient
    (s : List ((pullback g g).presheaf.stalk (F.rightImageMiddlePair G H z))) :
    (((F.rightFiberMiddleList G H z s ⟨_, hw⟩).map
      (F.rightAmbientMiddleStalkMap G H (F.tripleIncidenceToRightSupportProduct G H w)).hom).map
        (F.rightFirstStageTripleAmbientStalkIso G H w).hom.hom) =
      (F.rightFirstStageFiberTripleMiddleList G H z w hw s).map
        ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap
          (F.tripleIncidenceSixfoldInclusion G H w)).hom := by
  simp only [rightFiberMiddleList, rightFirstStageFiberTripleMiddleList, List.map_map]
  congr 1
  funext a
  exact ConcreteCategory.congr_hom (F.rightFirstStageFiberTripleMiddleStalk_square G H z w hw) a

/-- The fixed remaining Y list generates the literal first ambient diagonal ideal. -/
theorem rightFirstStageFiberTripleMiddleList_ambient_kernel [IsSeparated g]
    (s : List ((pullback g g).presheaf.stalk (F.rightImageMiddlePair G H z)))
    (hs : (pullback.diagonal g).ker.stalk (F.rightImageMiddlePair G H z) = Ideal.ofList s) :
    (correspondenceFirstDiagonalInclusion f g h i).ker.stalk
        (F.tripleIncidenceSixfoldInclusion G H w) =
      Ideal.ofList ((F.rightFirstStageFiberTripleMiddleList G H z w hw s).map
        ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap
          (F.tripleIncidenceSixfoldInclusion G H w)).hom) := by
  rw [ker_correspondenceFirstDiagonal, Scheme.IdealSheafData.stalk_comap,
    F.rightFirstStageFiberTripleMiddleList_kernel G H z w hw s hs, Ideal.map_ofList]

omit z hw in
/-- The original Z list is chosen at a branch. The fixed image-side Y list
is left untouched for the common two-list comparison. -/
theorem exists_rightFirstStageTripleSecondMiddleList
    [Smooth g] [IsSeparated g] [Smooth h] [IsSeparated h] :
    ∃ t : List ((pullback h h).presheaf.stalk
      (correspondenceSixfoldSecondMiddlePair f g h i (F.tripleIncidenceSixfoldInclusion G H w))),
      IsRegular ((pullback h h).presheaf.stalk
        (correspondenceSixfoldSecondMiddlePair f g h i
          (F.tripleIncidenceSixfoldInclusion G H w))) t ∧
      (correspondenceSecondAmbientInclusion f g h i).ker.stalk
        (F.tripleIncidenceSixfoldInclusion G H w) =
        Ideal.ofList (t.map ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap
          (F.tripleIncidenceSixfoldInclusion G H w)).hom) := by
  obtain ⟨_, t, _, ht, _, hkt⟩ := exists_common_middle_diagonalLists f g h i
    (F.tripleIncidenceFourfoldInclusion G H w)
  exact ⟨t, ht, hkt⟩

/-- Canonical total Tor uses the SAME fixed image-side Y list after actual
point transport. Signed tensor symmetry gives the original right order. -/
theorem exists_rightFirstStageFixedRemaining_total
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [LocallyOfFiniteType i]
    [Flat f] [Smooth g] [IsSeparated g] [Smooth h] [IsSeparated h] [Flat i]
    (hgen : w ∈ genericPoints (F.tripleIncidence G H))
    (s : List ((pullback g g).presheaf.stalk (F.rightImageMiddlePair G H z)))
    (hs : IsRegular ((pullback g g).presheaf.stalk (F.rightImageMiddlePair G H z)) s)
    (hker : (pullback.diagonal g).ker.stalk (F.rightImageMiddlePair G H z) = Ideal.ofList s) :
    let p := F.tripleIncidenceSixfoldInclusion G H w
    ∃ t : List ((pullback h h).presheaf.stalk (correspondenceSixfoldSecondMiddlePair f g h i p)),
      IsRegular ((pullback h h).presheaf.stalk
        (correspondenceSixfoldSecondMiddlePair f g h i p)) t ∧
      let t' := t.map ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap p).hom
      let s' := (F.rightFirstStageFiberTripleMiddleList G H z w hw s).map
        ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap p).hom
      let K := HomologicalComplex.tensorObj (_root_.ChainComplex.Koszul.chainComplex s')
        (_root_.ChainComplex.Koszul.coefficientComplex (F.tripleIncidenceSupportStalkModule G H w)
            t')
      ∃ hK : _root_.HomologicalComplex.ModuleLengthEuler.FiniteHomology K,
        (∀ n, Nonempty (F.tripleIncidenceTor G H w n ≅ K.homology n)) ∧
        F.tripleIncidenceTorCoefficient G H ⟨w, hgen⟩ =
            _root_.HomologicalComplex.ModuleLengthEuler.chainEuler K hK := by
  dsimp only
  obtain ⟨t, ht, hkt⟩ := F.exists_rightFirstStageTripleSecondMiddleList G H w
  let t' := t.map ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap
    (F.tripleIncidenceSixfoldInclusion G H w)).hom
  let s' := (F.rightFirstStageFiberTripleMiddleList G H z w hw s).map
    ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap
      (F.tripleIncidenceSixfoldInclusion G H w)).hom
  let M := F.tripleIncidenceSupportStalkModule G H w
  obtain ⟨hK, hTor, hEuler⟩ := F.triple_common_total_coefficient G H ⟨w, hgen⟩
    (F.rightFirstStageFiberTripleMiddleList G H z w hw s) t
    (F.rightFirstStageFiberTripleMiddleList_isRegular G H z w hw s hs).toIsWeaklyRegular
    ht.toIsWeaklyRegular
    (F.rightFirstStageFiberTripleMiddleList_ambient_kernel G H z w hw s hker) hkt
  refine ⟨t, ht, _root_.ChainComplex.Koszul.twoListOrder_finiteHomology M t' s' hK, ?_, ?_⟩
  · intro n
    obtain ⟨e⟩ := hTor n
    exact ⟨e ≪≫ (HomologicalComplex.homologyFunctor _ _ n).mapIso
      (_root_.ChainComplex.Koszul.twoListOrderIso M t' s')⟩
  · exact hEuler.trans (_root_.ChainComplex.Koszul.twoListOrder_chainEuler M t' s' hK)

omit z hw in
/-- The original right route and the canonical left-parenthesized route have
literally the same point on the original exterior triple support. -/
theorem rightFirstStageTripleCoefficientPoint :
    F.rightIntermediateToTripleSupport G H (F.tripleIncidenceToRightSupportProduct G H w) =
      (F.tripleIncidenceToLeftSupportProduct G H ≫ F.leftIntermediateToTripleSupport G H) w :=
  congrArg (fun a => a w) (F.tripleToRightSupport_coefficient G H)

omit z hw in
/-- Actual exterior-support point congruence transports the coefficient ring. -/
def rightFirstStageTripleCoefficientPointStalkIso :
    (F.tripleSupportProduct G H).presheaf.stalk
        (F.rightIntermediateToTripleSupport G H (F.tripleIncidenceToRightSupportProduct G H w)) ≅
      (F.tripleSupportProduct G H).presheaf.stalk
        ((F.tripleIncidenceToLeftSupportProduct G H ≫ F.leftIntermediateToTripleSupport G H) w) :=
  (F.tripleSupportProduct G H).presheaf.stalkCongr
    (.of_eq (F.rightFirstStageTripleCoefficientPoint G H w))

omit z hw in
/-- The original coefficient-support scalar map commutes with the actual
first-stage-to-canonical ambient point congruence. -/
theorem rightFirstStageTripleCoefficientStalk_square :
    (F.rightFirstStageTripleAmbientStalkIso G H w).hom ≫
        Intersection.coefficientStalkMap
          (correspondenceSecondDiagonalInclusion f g h i ≫
            correspondenceFirstDiagonalInclusion f g h i)
          (F.tripleIncidenceFourfoldInclusion G H w) (F.tripleSupportProductInclusion G H)
          ((F.tripleIncidenceToLeftSupportProduct G H ≫ F.leftIntermediateToTripleSupport G H) w)
          (Intersection.point_eq _ _ _ _ (F.tripleIncidence_sixfold_isPullback G H) w) =
      Intersection.coefficientStalkMap (correspondenceSecondAmbientInclusion f g h i)
        (F.rightIntermediateSupportInclusion G H (F.tripleIncidenceToRightSupportProduct G H w))
        (F.tripleSupportProductInclusion G H)
        (F.rightIntermediateToTripleSupport G H (F.tripleIncidenceToRightSupportProduct G H w))
        (Intersection.point_eq _ _ _ _ (F.rightIntermediate_ambient_isPullback G H)
          (F.tripleIncidenceToRightSupportProduct G H w)) ≫
        (F.rightFirstStageTripleCoefficientPointStalkIso G H w).hom :=
  rightAlignedStalkMap_two_points_square (F.tripleSupportProductInclusion G H) _ _
    (F.rightFirstStageTripleCoefficientPoint G H w) _ _
    (F.rightFirstStageTripleAmbientPoint G H w)
    (Intersection.point_eq _ _ _ _ (F.rightIntermediate_ambient_isPullback G H)
      (F.tripleIncidenceToRightSupportProduct G H w))
    (Intersection.point_eq _ _ _ _ (F.tripleIncidence_sixfold_isPullback G H) w)

omit z hw in
/-- Both actual ambient and exterior-support point congruences give the
coefficient module isomorphism with the exact canonical scalar action. -/
def rightFirstStageTripleCoefficientStalkIso :
    Intersection.coefficientStalkModule (correspondenceSecondAmbientInclusion f g h i)
        (F.rightIntermediateSupportInclusion G H (F.tripleIncidenceToRightSupportProduct G H w))
        (F.tripleSupportProductInclusion G H)
        (F.rightIntermediateToTripleSupport G H (F.tripleIncidenceToRightSupportProduct G H w))
        (Intersection.point_eq _ _ _ _ (F.rightIntermediate_ambient_isPullback G H)
          (F.tripleIncidenceToRightSupportProduct G H w)) ≅
      (ModuleCat.restrictScalars (F.rightFirstStageTripleAmbientStalkIso G H w).hom.hom).obj
        (F.tripleIncidenceSupportStalkModule G H w) := by
  let a := Intersection.coefficientStalkMap (correspondenceSecondAmbientInclusion f g h i)
    (F.rightIntermediateSupportInclusion G H (F.tripleIncidenceToRightSupportProduct G H w))
    (F.tripleSupportProductInclusion G H)
    (F.rightIntermediateToTripleSupport G H (F.tripleIncidenceToRightSupportProduct G H w))
    (Intersection.point_eq _ _ _ _ (F.rightIntermediate_ambient_isPullback G H)
      (F.tripleIncidenceToRightSupportProduct G H w))
  let b := Intersection.coefficientStalkMap
    (correspondenceSecondDiagonalInclusion f g h i ≫ correspondenceFirstDiagonalInclusion f g h i)
    (F.tripleIncidenceFourfoldInclusion G H w) (F.tripleSupportProductInclusion G H)
    ((F.tripleIncidenceToLeftSupportProduct G H ≫ F.leftIntermediateToTripleSupport G H) w)
    (Intersection.point_eq _ _ _ _ (F.tripleIncidence_sixfold_isPullback G H) w)
  exact _root_.ModuleCat.TorComparison.ringModuleIso
    (F.rightFirstStageTripleAmbientStalkIso G H w).commRingCatIsoToRingEquiv
    (F.rightFirstStageTripleCoefficientPointStalkIso G H w).commRingCatIsoToRingEquiv
    a.hom b.hom
    (fun r => (ConcreteCategory.congr_hom
      (F.rightFirstStageTripleCoefficientStalk_square G H w) r).symm)

omit z hw in
/-- Genuine supported Tor, after its literal ambient restriction, is the
homology of the actual second-diagonal coefficient Koszul resolution. -/
def rightFirstStageSupportedKoszulHomologyIso [IsSeparated h]
    (t : List ((correspondenceSixfoldAmbient f g h i).presheaf.stalk
      (F.rightIntermediateAmbientInclusion G H (F.tripleIncidenceToRightSupportProduct G H w))))
    (hker : RingHom.ker ((correspondenceSecondAmbientInclusion f g h i).stalkMap
      (F.rightIntermediateSupportInclusion G H
        (F.tripleIncidenceToRightSupportProduct G H w))).hom =
        Ideal.ofList t)
    (ht : IsRegular ((correspondenceSixfoldAmbient f g h i).presheaf.stalk
      (F.rightIntermediateAmbientInclusion G H (F.tripleIncidenceToRightSupportProduct G H w))) t)
    (n : ℕ) :
    (ModuleCat.restrictScalars ((F.rightIntermediateAmbientInclusion G H).stalkMap
      (F.tripleIncidenceToRightSupportProduct G H w)).hom).obj
        (F.rightFirstStageSupportedStalkTor G H (F.tripleIncidenceToRightSupportProduct G H w) n) ≅
      (_root_.ChainComplex.Koszul.coefficientComplex
        (Intersection.coefficientStalkModule (correspondenceSecondAmbientInclusion f g h i)
          (F.rightIntermediateSupportInclusion G H (F.tripleIncidenceToRightSupportProduct G H w))
          (F.tripleSupportProductInclusion G H)
          (F.rightIntermediateToTripleSupport G H (F.tripleIncidenceToRightSupportProduct G H w))
          (Intersection.point_eq _ _ _ _ (F.rightIntermediate_ambient_isPullback G H)
            (F.tripleIncidenceToRightSupportProduct G H w))) t).homology n :=
  Intersection.closedIntersectionSupportedStalkTorRestrictIso
    (correspondenceSecondAmbientInclusion f g h i) (F.tripleSupportProductInclusion G H)
    (F.rightIntermediateSupportInclusion G H) (F.rightIntermediateToTripleSupport G H)
    (F.rightIntermediate_ambient_isPullback G H) (F.tripleIncidenceToRightSupportProduct G H w) n ≪≫
      Intersection.torIsoHomology (correspondenceSecondAmbientInclusion f g h i)
        (F.rightIntermediateSupportInclusion G H (F.tripleIncidenceToRightSupportProduct G H w))
        (F.tripleSupportProductInclusion G H)
        (F.rightIntermediateToTripleSupport G H (F.tripleIncidenceToRightSupportProduct G H w))
        (Intersection.point_eq _ _ _ _ (F.rightIntermediate_ambient_isPullback G H)
          (F.tripleIncidenceToRightSupportProduct G H w)) t hker ht n

omit z hw in
/-- Supported right-first-stage Tor is actual Z-list homology in the canonical
ambient, with both the original support action and the point-congruence map retained. -/
def rightFirstStageSupportedCanonicalHomologyIso [IsSeparated h]
    (t : List (F.tripleIncidenceAmbientStalk G H w))
    (hker : (correspondenceSecondAmbientInclusion f g h i).ker.stalk
      (F.tripleIncidenceSixfoldInclusion G H w) = Ideal.ofList t)
    (ht : IsRegular (F.tripleIncidenceAmbientStalk G H w) t) (n : ℕ) :
    (ModuleCat.restrictScalars ((F.rightIntermediateAmbientInclusion G H).stalkMap
      (F.tripleIncidenceToRightSupportProduct G H w)).hom).obj
        (F.rightFirstStageSupportedStalkTor G H (F.tripleIncidenceToRightSupportProduct G H w) n) ≅
      (ModuleCat.restrictScalars (F.rightFirstStageTripleAmbientStalkIso G H w).hom.hom).obj
        ((_root_.ChainComplex.Koszul.coefficientComplex (F.tripleIncidenceSupportStalkModule G H w)
            t).homology n) := by
  let e := F.rightFirstStageTripleAmbientStalkIso G H w
  let t₀ := t.map e.inv.hom
  have hmap : t₀.map e.hom.hom = t := by
    dsimp only [t₀]
    rw [List.map_map]
    change t.map (fun a => e.hom (e.inv a)) = t
    simp only [Iso.inv_hom_id_apply]
    exact List.map_id t
  have ht₀ : IsRegular ((correspondenceSixfoldAmbient f g h i).presheaf.stalk
      (F.rightIntermediateAmbientInclusion G H
        (F.tripleIncidenceToRightSupportProduct G H w))) t₀ :=
    stalkCongr_regular (F.rightFirstStageTripleAmbientPoint G H w).symm t ht
  have hk₀ : RingHom.ker ((correspondenceSecondAmbientInclusion f g h i).stalkMap
      (F.rightIntermediateSupportInclusion G H
        (F.tripleIncidenceToRightSupportProduct G H w))).hom =
        Ideal.ofList t₀ := by
    rw [← (correspondenceSecondAmbientInclusion f g h i).ker_stalk]
    exact stalkCongr_kernel (correspondenceSecondAmbientInclusion f g h i).ker
      (F.rightFirstStageTripleAmbientPoint G H w).symm t hker
  exact F.rightFirstStageSupportedKoszulHomologyIso G H w t₀ hk₀ ht₀ n ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso
      (_root_.ChainComplex.Koszul.coefficientIso (F.rightFirstStageTripleCoefficientStalkIso G H w)
          t₀) ≪≫
    _root_.ChainComplex.Koszul.coefficientRestrictHomologyIso e.hom.hom
      (F.tripleIncidenceSupportStalkModule G H w) t₀ n ≪≫
    (ModuleCat.restrictScalars e.hom.hom).mapIso
      ((HomologicalComplex.homologyFunctor _ _ n).mapIso
        (eqToIso (congrArg
          (_root_.ChainComplex.Koszul.coefficientComplex (F.tripleIncidenceSupportStalkModule G H
              w)) hmap)))

/-- Each genuine supported-Tor remaining homology length equals the matching
homology-layer length of the canonical two-list total, using the original fixed list. -/
theorem rightFirstStageSourceCanonicalRemaining_length [IsSeparated h]
    (s : List ((pullback g g).presheaf.stalk (F.rightImageMiddlePair G H z)))
    (t : List (F.tripleIncidenceAmbientStalk G H w))
    (hker : (correspondenceSecondAmbientInclusion f g h i).ker.stalk
      (F.tripleIncidenceSixfoldInclusion G H w) = Ideal.ofList t)
    (ht : IsRegular (F.tripleIncidenceAmbientStalk G H w) t) (n r : ℕ) :
    Module.length ((F.rightIntermediateSupportProduct G H).presheaf.stalk
      (F.tripleIncidenceToRightSupportProduct G H w))
      ((_root_.ChainComplex.Koszul.coefficientComplex
        (F.rightFirstStageSupportedStalkTor G H (F.tripleIncidenceToRightSupportProduct G H w) n)
        ((F.rightFiberMiddleList G H z s ⟨_, hw⟩).map
          ((F.rightSupportMiddlePair G H).stalkMap
            (F.tripleIncidenceToRightSupportProduct G H w)).hom)).homology r) =
    Module.length (F.tripleIncidenceAmbientStalk G H w)
      ((_root_.ChainComplex.Koszul.coefficientComplex
        ((_root_.ChainComplex.Koszul.coefficientComplex (F.tripleIncidenceSupportStalkModule G H w)
            t).homology n)
        ((F.rightFirstStageFiberTripleMiddleList G H z w hw s).map
          ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap
            (F.tripleIncidenceSixfoldInclusion G H w)).hom)).homology r) := by
  let x := F.tripleIncidenceToRightSupportProduct G H w
  let a := ((F.rightIntermediateAmbientInclusion G H).stalkMap x).hom
  let s₀ := (F.rightFiberMiddleList G H z s ⟨_, hw⟩).map
    (F.rightAmbientMiddleStalkMap G H x).hom
  let e := F.rightFirstStageTripleAmbientStalkIso G H w
  let M := F.rightFirstStageSupportedStalkTor G H x n
  let N := (_root_.ChainComplex.Koszul.coefficientComplex (F.tripleIncidenceSupportStalkModule G H
      w) t).homology n
  have hsource := F.rightAmbientMiddleList_map G H x
    (F.rightFiberMiddleList G H z s ⟨_, hw⟩)
  have hcanonical := F.rightFirstStageFiberTripleMiddleList_ambient G H z w hw s
  calc
    _ = Module.length _ ((_root_.ChainComplex.Koszul.coefficientComplex M (s₀.map a)).homology r) :=
        by
      rw [hsource]
    _ = Module.length _
        ((_root_.ChainComplex.Koszul.coefficientComplex ((ModuleCat.restrictScalars a).obj M)
            s₀).homology r) :=
      (_root_.ChainComplex.Koszul.coefficientRestrict_length a
        ((F.rightIntermediateAmbientInclusion G H).stalkMap_surjective x) M s₀ r).symm
    _ = Module.length _
        ((_root_.ChainComplex.Koszul.coefficientComplex ((ModuleCat.restrictScalars e.hom.hom).obj
            N) s₀).homology r) :=
      ((HomologicalComplex.homologyFunctor _ _ r).mapIso
        (_root_.ChainComplex.Koszul.coefficientIso (F.rightFirstStageSupportedCanonicalHomologyIso G
            H w t hker ht n)
          s₀)).toLinearEquiv.length_eq
    _ = Module.length _ ((_root_.ChainComplex.Koszul.coefficientComplex N (s₀.map
        e.hom.hom)).homology r) :=
      _root_.ChainComplex.Koszul.coefficientRestrict_length e.hom.hom
          e.commRingCatIsoToRingEquiv.surjective N s₀ r
    _ = _ := by rw [hcanonical]

private theorem finiteHomology_of_source_lengths {R T : Type u} [CommRing R] [CommRing T]
    {C : ChainComplex (ModuleCat.{u} R) ℕ} {D : ChainComplex (ModuleCat.{u} T) ℕ}
    (hC : _root_.HomologicalComplex.ModuleLengthEuler.FiniteHomology C)
    (h : ∀ r, Module.length R (C.homology r) = Module.length T (D.homology r)) :
    _root_.HomologicalComplex.ModuleLengthEuler.FiniteHomology D where
  finite_length r := by rw [← h r]; exact hC.finite_length r
  finite_support := by simpa only [show (fun r => Module.length R (C.homology r)) =
    (fun r => Module.length T (D.homology r)) from funext h] using hC.finite_support

private theorem source_chainEuler_eq_of_lengths {R T : Type u} [CommRing R] [CommRing T]
    {C : ChainComplex (ModuleCat.{u} R) ℕ} {D : ChainComplex (ModuleCat.{u} T) ℕ}
    (h : ∀ r, Module.length R (C.homology r) = Module.length T (D.homology r))
    (hC : _root_.HomologicalComplex.ModuleLengthEuler.FiniteHomology C) (hD :
        _root_.HomologicalComplex.ModuleLengthEuler.FiniteHomology D) :
    _root_.HomologicalComplex.ModuleLengthEuler.chainEuler C hC =
        _root_.HomologicalComplex.ModuleLengthEuler.chainEuler D hD := by
  unfold _root_.HomologicalComplex.ModuleLengthEuler.chainEuler
      _root_.HomologicalComplex.ModuleLengthEuler.homologyEuler
      _root_.HomologicalComplex.ModuleLengthEuler.signedLengthSum
  apply finsum_congr
  intro r
  simp only [_root_.HomologicalComplex.ModuleLengthEuler.integerLength, h r]

omit z hw in
/-- The actual bounded hyperhomology theorem identifies the original supported
Tor outer Euler sum with canonical triple Tor. The remaining list is precisely
the one fixed at the original image point; no equality or finite-length premise
is added to perform the attachment. -/
theorem rightFirstStageSourceRemainingEuler_eq_tripleCoefficient
    [S.IsSeparated] [IsSeparated f] [IsSeparated g] [IsSeparated h] [IsSeparated i]
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [LocallyOfFiniteType i]
    [Flat f] [Smooth g] [Smooth h] [Flat i]
    [IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i)]
    (V : (F.rightIntermediateImageProduct G H).affineOpens)
    (p : Spec Γ(F.rightIntermediateImageProduct G H, V))
    [IsNoetherianRing ((F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p))]
    (y : F.rightImageIncidence G H) (hy : y ∈ genericPoints (F.rightImageIncidence G H))
    (hp : V.2.fromSpec p = F.rightImageIncidenceInclusion G H y)
    (hw : F.rightIntermediateImageMap G H (F.tripleIncidenceToRightSupportProduct G H w) =
      V.2.fromSpec p)
    (hgen : w ∈ genericPoints (F.tripleIncidence G H))
    (s : List ((pullback g g).presheaf.stalk (F.rightImageMiddlePair G H (V.2.fromSpec p))))
    (hs : IsRegular ((pullback g g).presheaf.stalk (F.rightImageMiddlePair G H (V.2.fromSpec p))) s)
    (hker : (pullback.diagonal g).ker.stalk
      (F.rightImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s) :
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
      F.rightFirstStageSourceRemainingEuler G H V p s y hy hp hker ⟨_, hw⟩ n) =
      F.tripleIncidenceTorCoefficient G H ⟨w, hgen⟩ := by
  classical
  obtain ⟨t, ht, hkt⟩ := F.exists_rightFirstStageTripleSecondMiddleList G H w
  let t' : List (F.tripleIncidenceAmbientStalk G H w) :=
    t.map ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap
    (F.tripleIncidenceSixfoldInclusion G H w)).hom
  let s' : List (F.tripleIncidenceAmbientStalk G H w) :=
    (F.rightFirstStageFiberTripleMiddleList G H (V.2.fromSpec p) w hw s).map
    ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap
      (F.tripleIncidenceSixfoldInclusion G H w)).hom
  let K := _root_.ChainComplex.Koszul.coefficientComplex (F.tripleIncidenceSupportStalkModule G H w)
      t'
  have ht' : IsRegular (F.tripleIncidenceAmbientStalk G H w) t' :=
    (common_middle_diagonalLists_isRegular f g h i
      (F.tripleIncidenceFourfoldInclusion G H w)
      (F.rightFirstStageFiberTripleMiddleList G H (V.2.fromSpec p) w hw s) t
      (F.rightFirstStageFiberTripleMiddleList_isRegular
        G H (V.2.fromSpec p) w hw s hs).toIsWeaklyRegular
      ht.toIsWeaklyRegular
      (F.rightFirstStageFiberTripleMiddleList_ambient_kernel
        G H (V.2.fromSpec p) w hw s hker) hkt).2
  let C := fun n => F.rightFirstStageSourceRemainingKoszul G H V p s ⟨_, hw⟩ n
  let D := fun n => _root_.ChainComplex.Koszul.coefficientComplex (K.homology n) s'
  have hC (n : ℕ) : _root_.HomologicalComplex.ModuleLengthEuler.FiniteHomology (C n) :=
    F.rightFirstStageSourceRemaining_finiteHomology G H V p s n
      (F.rightFirstStageWholeRemaining_finiteHomology G H V p y hy hp s hker n) ⟨_, hw⟩
  have hlen (n r : ℕ) : Module.length _ ((C n).homology r) =
      Module.length _ ((D n).homology r) :=
    F.rightFirstStageSourceCanonicalRemaining_length G H (V.2.fromSpec p) w hw s t' hkt ht' n r
  have hD (n : ℕ) : _root_.HomologicalComplex.ModuleLengthEuler.FiniteHomology (D n) :=
    finiteHomology_of_source_lengths (hC n) (hlen n)
  have hE (n : ℕ) :
      F.rightFirstStageSourceRemainingEuler G H V p s y hy hp hker ⟨_, hw⟩ n =
        _root_.HomologicalComplex.ModuleLengthEuler.chainEuler (D n) (hD n) :=
    source_chainEuler_eq_of_lengths (hlen n) (hC n) (hD n)
  have hK (n : ℕ) (hn : t'.length < n) : K.ExactAt n :=
    HomologicalComplex.ExactAt.of_isZero
      (_root_.ChainComplex.Koszul.coefficient_isZero_X (F.tripleIncidenceSupportStalkModule G H w)
          t' n hn)
  obtain ⟨hTotal, hTotalEuler⟩ := _root_.ChainComplex.Koszul.bounded_koszulTensor_chainEuler K s'
      t'.length hK
    (fun n _ => hD n)
  obtain ⟨hCanonical, _, hCanonicalEuler⟩ := F.triple_common_total_coefficient G H ⟨w, hgen⟩
    (F.rightFirstStageFiberTripleMiddleList G H (V.2.fromSpec p) w hw s) t
    (F.rightFirstStageFiberTripleMiddleList_isRegular
        G H (V.2.fromSpec p) w hw s hs).toIsWeaklyRegular
    ht.toIsWeaklyRegular
    (F.rightFirstStageFiberTripleMiddleList_ambient_kernel G H (V.2.fromSpec p) w hw s hker) hkt
  have hRightTotalEuler := hCanonicalEuler.trans
    (_root_.ChainComplex.Koszul.twoListOrder_chainEuler (F.tripleIncidenceSupportStalkModule G H w)
        t' s' hCanonical)
  have hzero (n : ℕ) (hn : t'.length < n) : _root_.HomologicalComplex.ModuleLengthEuler.chainEuler
      (D n) (hD n) = 0 := by
    have : Subsingleton (K.homology n) := ModuleCat.subsingleton_of_isZero (hK n hn).isZero_homology
    exact _root_.ChainComplex.Koszul.koszulDimension_chainEuler_zero_of_subsingleton (K.homology n)
        s' (hD n)
  calc
    _ = ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * _root_.HomologicalComplex.ModuleLengthEuler.chainEuler (D n) (hD n)
        := by
      apply finsum_congr
      intro n
      rw [hE]
    _ = ∑ n ∈ Finset.range (t'.length + 1),
        (-1 : ℤ) ^ n * _root_.HomologicalComplex.ModuleLengthEuler.chainEuler (D n) (hD n) := by
      apply finsum_eq_sum_of_support_subset
      intro n hn
      apply Finset.mem_range.mpr
      by_contra h
      exact hn (by
        change (-1 : ℤ) ^ n * _root_.HomologicalComplex.ModuleLengthEuler.chainEuler (D n) (hD n) =
            0
        rw [hzero n (by omega), mul_zero])
    _ = ∑ n : Fin (t'.length + 1),
        (-1 : ℤ) ^ (n : ℕ) * _root_.HomologicalComplex.ModuleLengthEuler.chainEuler (D n) (hD n) :=
            by
      exact (Fin.sum_univ_eq_sum_range _ _).symm
    _ = _root_.HomologicalComplex.ModuleLengthEuler.chainEuler (HomologicalComplex.tensorObj
        (_root_.ChainComplex.Koszul.chainComplex s') K)
        hTotal := hTotalEuler.symm
    _ = _ := hRightTotalEuler.symm


omit z w hw in
/-- Every point of the entire original finite fiber acquires its genuine generic
triple-incidence lift, and its full supported-Tor Euler sum is the canonical
coefficient of that lift. Genericity and the lift are derived from geometry. -/
theorem rightFirstStageSourceRemainingEuler_exists_tripleLift
    [S.IsSeparated] [IsSeparated f] [IsSeparated g] [IsSeparated h] [IsSeparated i]
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [LocallyOfFiniteType i]
    [Flat f] [Smooth g] [Smooth h] [Flat i]
    [IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i)]
    (V : (F.rightIntermediateImageProduct G H).affineOpens)
    (p : Spec Γ(F.rightIntermediateImageProduct G H, V))
    [IsNoetherianRing ((F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p))]
    (y : F.rightImageIncidence G H) (hy : y ∈ genericPoints (F.rightImageIncidence G H))
    (hp : V.2.fromSpec p = F.rightImageIncidenceInclusion G H y)
    (s : List ((pullback g g).presheaf.stalk (F.rightImageMiddlePair G H (V.2.fromSpec p))))
    (hs : IsRegular ((pullback g g).presheaf.stalk (F.rightImageMiddlePair G H (V.2.fromSpec p))) s)
    (hker : (pullback.diagonal g).ker.stalk
      (F.rightImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s)
    (x : {v : F.rightIntermediateSupportProduct G H //
      F.rightIntermediateImageMap G H v = V.2.fromSpec p}) :
    ∃ q : genericPoints (F.tripleIncidence G H),
      F.tripleIncidenceToRightSupportProduct G H q.1 = x.1 ∧
      (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
        F.rightFirstStageSourceRemainingEuler G H V p s y hy hp hker x n) =
        F.tripleIncidenceTorCoefficient G H q := by
  rcases x with ⟨x, hx⟩
  obtain ⟨w, hgen, _, hwx⟩ := F.rightImageIncidenceFiber_lift_generic G H y hy x (hx.trans hp)
  subst x
  exact ⟨⟨w, hgen⟩, rfl,
    F.rightFirstStageSourceRemainingEuler_eq_tripleCoefficient G H w V p y hy hp hx hgen s hs hker⟩

omit z w hw in
/-- The actual finite pushforward outer sum is the residue-weighted canonical
triple coefficient on every branch of its original fiber. This attaches the
source side of the projection to the true total before any cycle replacement. -/
theorem rightFirstStageRemainingProjection_to_tripleCoefficient
    [S.IsSeparated] [IsSeparated f] [IsSeparated g] [IsSeparated h] [IsSeparated i]
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [LocallyOfFiniteType i]
    [Flat f] [Smooth g] [Smooth h] [Flat i]
    [IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i)]
    (V : (F.rightIntermediateImageProduct G H).affineOpens)
    (p : Spec Γ(F.rightIntermediateImageProduct G H, V))
    [IsNoetherianRing ((F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p))]
    (y : F.rightImageIncidence G H) (hy : y ∈ genericPoints (F.rightImageIncidence G H))
    (hp : V.2.fromSpec p = F.rightImageIncidenceInclusion G H y)
    (s : List ((pullback g g).presheaf.stalk (F.rightImageMiddlePair G H (V.2.fromSpec p))))
    (hs : IsRegular ((pullback g g).presheaf.stalk (F.rightImageMiddlePair G H (V.2.fromSpec p))) s)
    (hker : (pullback.diagonal g).ker.stalk
      (F.rightImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s) :
    ∃ lift : {v : F.rightIntermediateSupportProduct G H //
        F.rightIntermediateImageMap G H v = V.2.fromSpec p} →
        genericPoints (F.tripleIncidence G H),
      (∀ x, F.tripleIncidenceToRightSupportProduct G H (lift x).1 = x.1) ∧
      (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
        F.rightFirstStagePushforwardRemainingEuler G H V p s y hy hp hker n) =
      ∑ᶠ x : {v : F.rightIntermediateSupportProduct G H //
        F.rightIntermediateImageMap G H v = V.2.fromSpec p},
        ((F.rightIntermediateImageMap G H).residueDegree x.1 : ℤ) *
          F.tripleIncidenceTorCoefficient G H (lift x) := by
  classical
  choose lift hlift hEuler using
    F.rightFirstStageSourceRemainingEuler_exists_tripleLift G H V p y hy hp s hs hker
  refine ⟨lift, hlift,
    (F.rightFirstStageRemainingOuterProjectionEuler G H V p s y hy hp hker).trans ?_⟩
  apply finsum_congr
  intro x
  rw [hEuler x]

end Motivic.FiniteCorrespondenceGenerator
