/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.WholeFiberTorRemainingOuterSum
public import Motivic.AlgebraicGeometry.Correspondences.TripleTwoListTorComparison
public import Motivic.Algebra.Homology.KoszulHyperhomologyBounded
public import Motivic.Algebra.Homology.TorComparison.RingEquiv

/-!
# The fixed image-side remaining list in canonical triple Tor

The same originally chosen smooth remaining list is transported to each genuine
triple-incidence lift by actual middle-point equalities. Its regularity and
kernel presentation travel with that list. The literal ambient scalar square
is retained before comparing supported Tor with first-list Koszul homology.
The actual bounded hyperhomology Euler theorem then attaches each original
source outer sum to canonical triple Tor, retaining the original finite fiber
and its residue weights. Cycle replacement remains a separate step.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingTheory.Sequence

universe u

namespace Motivic.FiniteCorrespondenceGenerator

/-- Point congruence preserves the regularity of the transported stalk list. -/
theorem stalkCongr_regular {Q : Scheme.{u}} {z z' : Q} (e : z = z')
    (s : List (Q.presheaf.stalk z)) (hs : IsRegular (Q.presheaf.stalk z) s) :
    IsRegular (Q.presheaf.stalk z')
      (s.map (Q.presheaf.stalkCongr (.of_eq e)).hom.hom) := by
  subst z'
  simpa using hs

/-- Point congruence preserves the literal stalk-ideal presentation. -/
theorem stalkCongr_kernel {Q : Scheme.{u}} (J : Q.IdealSheafData)
    {z z' : Q} (e : z = z') (s : List (Q.presheaf.stalk z))
    (hs : J.stalk z = Ideal.ofList s) :
    J.stalk z' = Ideal.ofList (s.map (Q.presheaf.stalkCongr (.of_eq e)).hom.hom) := by
  subst z'
  simpa using hs

private theorem alignedStalkMap_point_square {P Q : Scheme.{u}} (q : P ⟶ Q)
    (x x' : P) (e : x = x') (z z' : Q) (ez : z = z') (hz : z' = q x) :
    (Q.presheaf.stalkCongr (.of_eq ez)).hom ≫ Graph.alignedStalkMap q x z' hz ≫
        (P.presheaf.stalkCongr (.of_eq e)).hom =
      Graph.alignedStalkMap q x' z (ez.trans (hz.trans (congrArg q e))) := by
  subst x'
  subst z'
  simp

private theorem alignedStalkMap_source_square {P Q : Scheme.{u}} (q : P ⟶ Q)
    (x : P) (z z' : Q) (e : z = z') (hz : z = q x) (hz' : z' = q x) :
    (Q.presheaf.stalkCongr (.of_eq e)).hom ≫ Graph.alignedStalkMap q x z' hz' =
      Graph.alignedStalkMap q x z hz := by
  subst z'
  simp

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)
  (z : F.leftIntermediateImageProduct G H) (w : F.tripleIncidence G H)
  (hw : F.leftIntermediateImageMap G H (F.tripleIncidenceToLeftSupportProduct G H w) = z)

include hw in
/-- The fixed image middle point equals the actual common six-factor middle point. -/
theorem firstStageFiberTripleMiddlePoint :
    F.leftImageMiddlePair G H z =
      correspondenceSixfoldSecondMiddlePair f g h i (F.tripleIncidenceSixfoldInclusion G H w) :=
  (F.leftFiberMiddlePoint G H z ⟨_, hw⟩).trans (F.tripleRemainingMiddlePoint G H w)

/-- Only the actual equality of original middle points transports the common list. -/
def firstStageFiberTripleMiddleStalkIso :
    (pullback h h).presheaf.stalk (F.leftImageMiddlePair G H z) ≅
      (pullback h h).presheaf.stalk
        (correspondenceSixfoldSecondMiddlePair f g h i (F.tripleIncidenceSixfoldInclusion G H w)) :=
  (pullback h h).presheaf.stalkCongr (.of_eq (F.firstStageFiberTripleMiddlePoint G H z w hw))

/-- The second original middle list at a source lift is the SAME target-chosen list. -/
def firstStageFiberTripleMiddleList
    (s : List ((pullback h h).presheaf.stalk (F.leftImageMiddlePair G H z))) :=
  s.map (F.firstStageFiberTripleMiddleStalkIso G H z w hw).hom.hom

/-- The regularity witness of the fixed smooth target list survives its actual point transport. -/
theorem firstStageFiberTripleMiddleList_isRegular
    (s : List ((pullback h h).presheaf.stalk (F.leftImageMiddlePair G H z)))
    (hs : IsRegular ((pullback h h).presheaf.stalk (F.leftImageMiddlePair G H z)) s) :
    IsRegular ((pullback h h).presheaf.stalk
      (correspondenceSixfoldSecondMiddlePair f g h i (F.tripleIncidenceSixfoldInclusion G H w)))
      (F.firstStageFiberTripleMiddleList G H z w hw s) :=
  stalkCongr_regular (F.firstStageFiberTripleMiddlePoint G H z w hw) s hs

/-- The same target list retains its literal original diagonal-kernel presentation. -/
theorem firstStageFiberTripleMiddleList_kernel
    (s : List ((pullback h h).presheaf.stalk (F.leftImageMiddlePair G H z)))
    (hs : (pullback.diagonal h).ker.stalk (F.leftImageMiddlePair G H z) = Ideal.ofList s) :
    (pullback.diagonal h).ker.stalk
        (correspondenceSixfoldSecondMiddlePair f g h i (F.tripleIncidenceSixfoldInclusion G H w)) =
      Ideal.ofList (F.firstStageFiberTripleMiddleList G H z w hw s) :=
  stalkCongr_kernel (pullback.diagonal h).ker
    (F.firstStageFiberTripleMiddlePoint G H z w hw) s hs

omit z hw in
/-- The two ambient descriptions give literally equal original points. -/
theorem firstStageTripleAmbientPoint :
    F.leftIntermediateAmbientInclusion G H (F.tripleIncidenceToLeftSupportProduct G H w) =
      F.tripleIncidenceSixfoldInclusion G H w :=
  congrArg (fun a => a w) (F.tripleToLeftSupport_ambient G H)

omit z hw in
/-- The first-stage and canonical triple ambient stalks differ only by
their actual point equality. -/
def firstStageTripleAmbientStalkIso :
    (correspondenceSixfoldAmbient f g h i).presheaf.stalk
        (F.leftIntermediateAmbientInclusion G H (F.tripleIncidenceToLeftSupportProduct G H w)) ≅
      F.tripleIncidenceAmbientStalk G H w :=
  (correspondenceSixfoldAmbient f g h i).presheaf.stalkCongr
    (.of_eq (F.firstStageTripleAmbientPoint G H w))

/-- The literal middle-to-ambient square preserves the fixed target list
before any Tor comparison. -/
theorem firstStageFiberTripleMiddleStalk_square :
    (F.leftFiberMiddleStalkIso G H z ⟨_, hw⟩).hom ≫
        F.leftAmbientMiddleStalkMap G H (F.tripleIncidenceToLeftSupportProduct G H w) ≫
        (F.firstStageTripleAmbientStalkIso G H w).hom =
      (F.firstStageFiberTripleMiddleStalkIso G H z w hw).hom ≫
        (correspondenceSixfoldSecondMiddlePair f g h i).stalkMap
          (F.tripleIncidenceSixfoldInclusion G H w) := by
  simpa only [leftFiberMiddleStalkIso, leftAmbientMiddleStalkMap,
    firstStageTripleAmbientStalkIso, firstStageFiberTripleMiddleStalkIso,
    Graph.alignedStalkMap] using
    (alignedStalkMap_point_square (correspondenceSixfoldSecondMiddlePair f g h i)
      (F.leftIntermediateAmbientInclusion G H (F.tripleIncidenceToLeftSupportProduct G H w))
      (F.tripleIncidenceSixfoldInclusion G H w) (F.firstStageTripleAmbientPoint G H w)
      (F.leftImageMiddlePair G H z)
      (F.leftSupportMiddlePair G H (F.tripleIncidenceToLeftSupportProduct G H w))
      (F.leftFiberMiddlePoint G H z ⟨_, hw⟩)
      (congrArg (fun a => a (F.tripleIncidenceToLeftSupportProduct G H w))
        (F.leftIntermediateAmbientInclusion_middlePair G H)).symm)


/-- The actual ambient image of the fixed list agrees with the canonical two-list image. -/
theorem firstStageFiberTripleMiddleList_ambient
    (s : List ((pullback h h).presheaf.stalk (F.leftImageMiddlePair G H z))) :
    (((F.leftFiberMiddleList G H z s ⟨_, hw⟩).map
      (F.leftAmbientMiddleStalkMap G H (F.tripleIncidenceToLeftSupportProduct G H w)).hom).map
        (F.firstStageTripleAmbientStalkIso G H w).hom.hom) =
      (F.firstStageFiberTripleMiddleList G H z w hw s).map
        ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap
          (F.tripleIncidenceSixfoldInclusion G H w)).hom := by
  simp only [leftFiberMiddleList, firstStageFiberTripleMiddleList, List.map_map]
  congr 1
  funext a
  exact ConcreteCategory.congr_hom (F.firstStageFiberTripleMiddleStalk_square G H z w hw) a

/-- The fixed second list generates the literal second ambient diagonal ideal. -/
theorem firstStageFiberTripleMiddleList_ambient_kernel [IsSeparated h]
    (s : List ((pullback h h).presheaf.stalk (F.leftImageMiddlePair G H z)))
    (hs : (pullback.diagonal h).ker.stalk (F.leftImageMiddlePair G H z) = Ideal.ofList s) :
    (correspondenceSecondAmbientInclusion f g h i).ker.stalk
        (F.tripleIncidenceSixfoldInclusion G H w) =
      Ideal.ofList ((F.firstStageFiberTripleMiddleList G H z w hw s).map
        ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap
          (F.tripleIncidenceSixfoldInclusion G H w)).hom) := by
  rw [ker_correspondenceSecondDiagonal, Scheme.IdealSheafData.stalk_comap,
    F.firstStageFiberTripleMiddleList_kernel G H z w hw s hs, Ideal.map_ofList]

omit z hw in
/-- Only the first original middle list is chosen at a branch. The fixed second
list is left untouched for the eventual common two-list comparison. -/
theorem exists_firstStageTripleFirstMiddleList [Smooth g] [IsSeparated g] :
    ∃ t : List ((pullback g g).presheaf.stalk
      (correspondenceSixfoldFirstMiddlePair f g h i (F.tripleIncidenceSixfoldInclusion G H w))),
      IsRegular ((pullback g g).presheaf.stalk
        (correspondenceSixfoldFirstMiddlePair f g h i
          (F.tripleIncidenceSixfoldInclusion G H w))) t ∧
      (correspondenceFirstDiagonalInclusion f g h i).ker.stalk
        (F.tripleIncidenceSixfoldInclusion G H w) =
        Ideal.ofList (t.map ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap
          (F.tripleIncidenceSixfoldInclusion G H w)).hom) := by
  let q := correspondenceSecondDiagonalInclusion f g h i
    (F.tripleIncidenceFourfoldInclusion G H w)
  let v := (pullback.fst (correspondenceTripleTarget f g h ≫ h) (pullback.fst h i ≫ h) ≫
    correspondenceTripleMiddle f g h) q
  have hv : pullback.diagonal g v =
      correspondenceSixfoldFirstMiddlePair f g h i (F.tripleIncidenceSixfoldInclusion G H w) :=
    congrArg (fun a => a q) (correspondenceSixfoldFirstDiagonal_isPullback f g h i).w
  have hex : ∃ t : List ((pullback g g).presheaf.stalk (pullback.diagonal g v)),
      IsRegular ((pullback g g).presheaf.stalk (pullback.diagonal g v)) t ∧
      (pullback.diagonal g).ker.stalk (pullback.diagonal g v) = Ideal.ofList t := by
    obtain ⟨t, ht, hker⟩ := Diagonal.exists_regular_kernel_of_smooth g v
    exact ⟨t, ht, ((pullback.diagonal g).ker_stalk v).trans hker⟩
  have hex' := (congrArg (fun a : (pullback g g : Scheme.{u}) =>
    ∃ t : List ((pullback g g).presheaf.stalk a),
      IsRegular ((pullback g g).presheaf.stalk a) t ∧
      (pullback.diagonal g).ker.stalk a = Ideal.ofList t) hv).mp hex
  obtain ⟨t, ht, hker⟩ := hex'
  refine ⟨t, ht, ?_⟩
  rw [ker_correspondenceFirstDiagonal, Scheme.IdealSheafData.stalk_comap, hker, Ideal.map_ofList]

/-- Canonical total Tor uses the SAME fixed image-side second list after actual
point transport; only the first middle list is chosen at this original branch. -/
theorem exists_firstStageFixedRemaining_total
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [LocallyOfFiniteType i]
    [Flat f] [Smooth g] [IsSeparated g] [Smooth h] [IsSeparated h] [Flat i]
    (hgen : w ∈ genericPoints (F.tripleIncidence G H))
    (s : List ((pullback h h).presheaf.stalk (F.leftImageMiddlePair G H z)))
    (hs : IsRegular ((pullback h h).presheaf.stalk (F.leftImageMiddlePair G H z)) s)
    (hker : (pullback.diagonal h).ker.stalk (F.leftImageMiddlePair G H z) = Ideal.ofList s) :
    let p := F.tripleIncidenceSixfoldInclusion G H w
    ∃ t : List ((pullback g g).presheaf.stalk (correspondenceSixfoldFirstMiddlePair f g h i p)),
      IsRegular ((pullback g g).presheaf.stalk
        (correspondenceSixfoldFirstMiddlePair f g h i p)) t ∧
      let t' := t.map ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap p).hom
      let s' := (F.firstStageFiberTripleMiddleList G H z w hw s).map
        ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap p).hom
      let K := HomologicalComplex.tensorObj (Koszul.chainComplex s')
        (Koszul.coefficientComplex (F.tripleIncidenceSupportStalkModule G H w) t')
      ∃ hK : LengthEuler.FiniteHomology K,
        (∀ n, Nonempty (F.tripleIncidenceTor G H w n ≅ K.homology n)) ∧
        F.tripleIncidenceTorCoefficient G H ⟨w, hgen⟩ = LengthEuler.chainEuler K hK := by
  dsimp only
  obtain ⟨t, ht, hkt⟩ := F.exists_firstStageTripleFirstMiddleList G H w
  exact ⟨t, ht, F.triple_common_total_coefficient G H ⟨w, hgen⟩ t
    (F.firstStageFiberTripleMiddleList G H z w hw s) ht.toIsWeaklyRegular
    (F.firstStageFiberTripleMiddleList_isRegular G H z w hw s hs).toIsWeaklyRegular hkt
    (F.firstStageFiberTripleMiddleList_ambient_kernel G H z w hw s hker)⟩

omit z hw in
/-- The original coefficient-support scalar map commutes with the actual
first-stage-to-canonical ambient point congruence. -/
theorem firstStageTripleCoefficientStalk_square :
    (F.firstStageTripleAmbientStalkIso G H w).hom ≫
        Intersection.coefficientStalkMap
          (correspondenceSecondDiagonalInclusion f g h i ≫
            correspondenceFirstDiagonalInclusion f g h i)
          (F.tripleIncidenceFourfoldInclusion G H w) (F.tripleSupportProductInclusion G H)
          ((F.tripleIncidenceToLeftSupportProduct G H ≫ F.leftIntermediateToTripleSupport G H) w)
          (Intersection.point_eq _ _ _ _ (F.tripleIncidence_sixfold_isPullback G H) w) =
      Intersection.coefficientStalkMap (correspondenceFirstDiagonalInclusion f g h i)
        (F.leftIntermediateSupportInclusion G H (F.tripleIncidenceToLeftSupportProduct G H w))
        (F.tripleSupportProductInclusion G H)
        (F.leftIntermediateToTripleSupport G H (F.tripleIncidenceToLeftSupportProduct G H w))
        (Intersection.point_eq _ _ _ _ (F.leftIntermediate_ambient_isPullback G H)
          (F.tripleIncidenceToLeftSupportProduct G H w)) :=
  alignedStalkMap_source_square (F.tripleSupportProductInclusion G H) _ _ _
    (F.firstStageTripleAmbientPoint G H w)
    (Intersection.point_eq _ _ _ _ (F.leftIntermediate_ambient_isPullback G H)
      (F.tripleIncidenceToLeftSupportProduct G H w))
    (Intersection.point_eq _ _ _ _ (F.tripleIncidence_sixfold_isPullback G H) w)

omit z hw in
/-- The original coefficient stalk is identical on elements and has the exact
canonical ambient action after the proved point-congruence scalar square. -/
def firstStageTripleCoefficientStalkIso :
    Intersection.coefficientStalkModule (correspondenceFirstDiagonalInclusion f g h i)
        (F.leftIntermediateSupportInclusion G H (F.tripleIncidenceToLeftSupportProduct G H w))
        (F.tripleSupportProductInclusion G H)
        (F.leftIntermediateToTripleSupport G H (F.tripleIncidenceToLeftSupportProduct G H w))
        (Intersection.point_eq _ _ _ _ (F.leftIntermediate_ambient_isPullback G H)
          (F.tripleIncidenceToLeftSupportProduct G H w)) ≅
      (ModuleCat.restrictScalars (F.firstStageTripleAmbientStalkIso G H w).hom.hom).obj
        (F.tripleIncidenceSupportStalkModule G H w) := by
  let a := Intersection.coefficientStalkMap (correspondenceFirstDiagonalInclusion f g h i)
    (F.leftIntermediateSupportInclusion G H (F.tripleIncidenceToLeftSupportProduct G H w))
    (F.tripleSupportProductInclusion G H)
    (F.leftIntermediateToTripleSupport G H (F.tripleIncidenceToLeftSupportProduct G H w))
    (Intersection.point_eq _ _ _ _ (F.leftIntermediate_ambient_isPullback G H)
      (F.tripleIncidenceToLeftSupportProduct G H w))
  let b := Intersection.coefficientStalkMap
    (correspondenceSecondDiagonalInclusion f g h i ≫ correspondenceFirstDiagonalInclusion f g h i)
    (F.tripleIncidenceFourfoldInclusion G H w) (F.tripleSupportProductInclusion G H)
    ((F.tripleIncidenceToLeftSupportProduct G H ≫ F.leftIntermediateToTripleSupport G H) w)
    (Intersection.point_eq _ _ _ _ (F.tripleIncidence_sixfold_isPullback G H) w)
  exact TorComparison.ringModuleIso
    (F.firstStageTripleAmbientStalkIso G H w).commRingCatIsoToRingEquiv (RingEquiv.refl _)
    a.hom b.hom
    (fun r => (ConcreteCategory.congr_hom (F.firstStageTripleCoefficientStalk_square G H w) r).symm)

omit z hw in
/-- Genuine supported Tor, after its literal ambient restriction, is the
homology of the actual first-diagonal coefficient Koszul resolution. -/
def firstStageSupportedKoszulHomologyIso [IsSeparated g]
    (t : List ((correspondenceSixfoldAmbient f g h i).presheaf.stalk
      (F.leftIntermediateAmbientInclusion G H (F.tripleIncidenceToLeftSupportProduct G H w))))
    (hker : RingHom.ker ((correspondenceFirstDiagonalInclusion f g h i).stalkMap
      (F.leftIntermediateSupportInclusion G H (F.tripleIncidenceToLeftSupportProduct G H w))).hom =
        Ideal.ofList t)
    (ht : IsRegular ((correspondenceSixfoldAmbient f g h i).presheaf.stalk
      (F.leftIntermediateAmbientInclusion G H (F.tripleIncidenceToLeftSupportProduct G H w))) t)
    (n : ℕ) :
    (ModuleCat.restrictScalars ((F.leftIntermediateAmbientInclusion G H).stalkMap
      (F.tripleIncidenceToLeftSupportProduct G H w)).hom).obj
        (F.firstStageSupportedStalkTor G H (F.tripleIncidenceToLeftSupportProduct G H w) n) ≅
      (Koszul.coefficientComplex
        (Intersection.coefficientStalkModule (correspondenceFirstDiagonalInclusion f g h i)
          (F.leftIntermediateSupportInclusion G H (F.tripleIncidenceToLeftSupportProduct G H w))
          (F.tripleSupportProductInclusion G H)
          (F.leftIntermediateToTripleSupport G H (F.tripleIncidenceToLeftSupportProduct G H w))
          (Intersection.point_eq _ _ _ _ (F.leftIntermediate_ambient_isPullback G H)
            (F.tripleIncidenceToLeftSupportProduct G H w))) t).homology n :=
  Intersection.closedIntersectionSupportedStalkTorRestrictIso
    (correspondenceFirstDiagonalInclusion f g h i) (F.tripleSupportProductInclusion G H)
    (F.leftIntermediateSupportInclusion G H) (F.leftIntermediateToTripleSupport G H)
    (F.leftIntermediate_ambient_isPullback G H) (F.tripleIncidenceToLeftSupportProduct G H w) n ≪≫
      Intersection.torIsoHomology (correspondenceFirstDiagonalInclusion f g h i)
        (F.leftIntermediateSupportInclusion G H (F.tripleIncidenceToLeftSupportProduct G H w))
        (F.tripleSupportProductInclusion G H)
        (F.leftIntermediateToTripleSupport G H (F.tripleIncidenceToLeftSupportProduct G H w))
        (Intersection.point_eq _ _ _ _ (F.leftIntermediate_ambient_isPullback G H)
          (F.tripleIncidenceToLeftSupportProduct G H w)) t hker ht n

omit z hw in
/-- Supported first-stage Tor is actual first-list homology in the canonical
ambient, with both the original support action and the point-congruence map retained. -/
def firstStageSupportedCanonicalHomologyIso [IsSeparated g]
    (t : List (F.tripleIncidenceAmbientStalk G H w))
    (hker : (correspondenceFirstDiagonalInclusion f g h i).ker.stalk
      (F.tripleIncidenceSixfoldInclusion G H w) = Ideal.ofList t)
    (ht : IsRegular (F.tripleIncidenceAmbientStalk G H w) t) (n : ℕ) :
    (ModuleCat.restrictScalars ((F.leftIntermediateAmbientInclusion G H).stalkMap
      (F.tripleIncidenceToLeftSupportProduct G H w)).hom).obj
        (F.firstStageSupportedStalkTor G H (F.tripleIncidenceToLeftSupportProduct G H w) n) ≅
      (ModuleCat.restrictScalars (F.firstStageTripleAmbientStalkIso G H w).hom.hom).obj
        ((Koszul.coefficientComplex (F.tripleIncidenceSupportStalkModule G H w) t).homology n) := by
  let e := F.firstStageTripleAmbientStalkIso G H w
  let t₀ := t.map e.inv.hom
  have hmap : t₀.map e.hom.hom = t := by
    dsimp only [t₀]
    rw [List.map_map]
    change t.map (fun a => e.hom (e.inv a)) = t
    simp only [Iso.inv_hom_id_apply]
    exact List.map_id t
  have ht₀ : IsRegular ((correspondenceSixfoldAmbient f g h i).presheaf.stalk
      (F.leftIntermediateAmbientInclusion G H (F.tripleIncidenceToLeftSupportProduct G H w))) t₀ :=
    stalkCongr_regular (F.firstStageTripleAmbientPoint G H w).symm t ht
  have hk₀ : RingHom.ker ((correspondenceFirstDiagonalInclusion f g h i).stalkMap
      (F.leftIntermediateSupportInclusion G H (F.tripleIncidenceToLeftSupportProduct G H w))).hom =
        Ideal.ofList t₀ := by
    rw [← (correspondenceFirstDiagonalInclusion f g h i).ker_stalk]
    exact stalkCongr_kernel (correspondenceFirstDiagonalInclusion f g h i).ker
      (F.firstStageTripleAmbientPoint G H w).symm t hker
  exact F.firstStageSupportedKoszulHomologyIso G H w t₀ hk₀ ht₀ n ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso
      (Koszul.coefficientIso (F.firstStageTripleCoefficientStalkIso G H w) t₀) ≪≫
    Koszul.coefficientRestrictHomologyIso e.hom.hom
      (F.tripleIncidenceSupportStalkModule G H w) t₀ n ≪≫
    (ModuleCat.restrictScalars e.hom.hom).mapIso
      ((HomologicalComplex.homologyFunctor _ _ n).mapIso
        (eqToIso (congrArg
          (Koszul.coefficientComplex (F.tripleIncidenceSupportStalkModule G H w)) hmap)))

/-- Each genuine supported-Tor remaining homology length equals the matching
homology-layer length of the canonical two-list total, using the original fixed list. -/
theorem firstStageSourceCanonicalRemaining_length [IsSeparated g]
    (s : List ((pullback h h).presheaf.stalk (F.leftImageMiddlePair G H z)))
    (t : List (F.tripleIncidenceAmbientStalk G H w))
    (hker : (correspondenceFirstDiagonalInclusion f g h i).ker.stalk
      (F.tripleIncidenceSixfoldInclusion G H w) = Ideal.ofList t)
    (ht : IsRegular (F.tripleIncidenceAmbientStalk G H w) t) (n r : ℕ) :
    Module.length ((F.leftIntermediateSupportProduct G H).presheaf.stalk
      (F.tripleIncidenceToLeftSupportProduct G H w))
      ((Koszul.coefficientComplex
        (F.firstStageSupportedStalkTor G H (F.tripleIncidenceToLeftSupportProduct G H w) n)
        ((F.leftFiberMiddleList G H z s ⟨_, hw⟩).map
          ((F.leftSupportMiddlePair G H).stalkMap
            (F.tripleIncidenceToLeftSupportProduct G H w)).hom)).homology r) =
    Module.length (F.tripleIncidenceAmbientStalk G H w)
      ((Koszul.coefficientComplex
        ((Koszul.coefficientComplex (F.tripleIncidenceSupportStalkModule G H w) t).homology n)
        ((F.firstStageFiberTripleMiddleList G H z w hw s).map
          ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap
            (F.tripleIncidenceSixfoldInclusion G H w)).hom)).homology r) := by
  let x := F.tripleIncidenceToLeftSupportProduct G H w
  let a := ((F.leftIntermediateAmbientInclusion G H).stalkMap x).hom
  let s₀ := (F.leftFiberMiddleList G H z s ⟨_, hw⟩).map
    (F.leftAmbientMiddleStalkMap G H x).hom
  let e := F.firstStageTripleAmbientStalkIso G H w
  let M := F.firstStageSupportedStalkTor G H x n
  let N := (Koszul.coefficientComplex (F.tripleIncidenceSupportStalkModule G H w) t).homology n
  have hsource := F.leftAmbientMiddleList_map G H x
    (F.leftFiberMiddleList G H z s ⟨_, hw⟩)
  have hcanonical := F.firstStageFiberTripleMiddleList_ambient G H z w hw s
  calc
    _ = Module.length _ ((Koszul.coefficientComplex M (s₀.map a)).homology r) := by
      rw [hsource]
    _ = Module.length _
        ((Koszul.coefficientComplex ((ModuleCat.restrictScalars a).obj M) s₀).homology r) :=
      (Koszul.coefficientRestrict_length a
        ((F.leftIntermediateAmbientInclusion G H).stalkMap_surjective x) M s₀ r).symm
    _ = Module.length _
        ((Koszul.coefficientComplex ((ModuleCat.restrictScalars e.hom.hom).obj N) s₀).homology r) :=
      ((HomologicalComplex.homologyFunctor _ _ r).mapIso
        (Koszul.coefficientIso (F.firstStageSupportedCanonicalHomologyIso G H w t hker ht n)
          s₀)).toLinearEquiv.length_eq
    _ = Module.length _ ((Koszul.coefficientComplex N (s₀.map e.hom.hom)).homology r) :=
      Koszul.coefficientRestrict_length e.hom.hom e.commRingCatIsoToRingEquiv.surjective N s₀ r
    _ = _ := by rw [hcanonical]

private theorem finiteHomology_of_source_lengths {R T : Type u} [CommRing R] [CommRing T]
    {C : ChainComplex (ModuleCat.{u} R) ℕ} {D : ChainComplex (ModuleCat.{u} T) ℕ}
    (hC : LengthEuler.FiniteHomology C)
    (h : ∀ r, Module.length R (C.homology r) = Module.length T (D.homology r)) :
    LengthEuler.FiniteHomology D where
  finite_length r := by rw [← h r]; exact hC.finite_length r
  finite_support := by simpa only [show (fun r => Module.length R (C.homology r)) =
    (fun r => Module.length T (D.homology r)) from funext h] using hC.finite_support

private theorem source_chainEuler_eq_of_lengths {R T : Type u} [CommRing R] [CommRing T]
    {C : ChainComplex (ModuleCat.{u} R) ℕ} {D : ChainComplex (ModuleCat.{u} T) ℕ}
    (h : ∀ r, Module.length R (C.homology r) = Module.length T (D.homology r))
    (hC : LengthEuler.FiniteHomology C) (hD : LengthEuler.FiniteHomology D) :
    LengthEuler.chainEuler C hC = LengthEuler.chainEuler D hD := by
  unfold LengthEuler.chainEuler LengthEuler.homologyEuler LengthEuler.signedLengthSum
  apply finsum_congr
  intro r
  simp only [LengthEuler.integerLength, h r]

omit z hw in
/-- The actual bounded hyperhomology theorem identifies the original supported
Tor outer Euler sum with canonical triple Tor. The remaining list is precisely
the one fixed at the original image point; no equality or finite-length premise
is added to perform the attachment. -/
theorem firstStageSourceRemainingEuler_eq_tripleCoefficient
    [S.IsSeparated] [IsSeparated f] [IsSeparated g] [IsSeparated h] [IsSeparated i]
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [LocallyOfFiniteType i]
    [Flat f] [Smooth g] [Smooth h] [Flat i]
    [IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i)]
    (V : (F.leftIntermediateImageProduct G H).affineOpens)
    (p : Spec Γ(F.leftIntermediateImageProduct G H, V))
    [IsNoetherianRing ((F.leftIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p))]
    (y : F.leftImageIncidence G H) (hy : y ∈ genericPoints (F.leftImageIncidence G H))
    (hp : V.2.fromSpec p = F.leftImageIncidenceInclusion G H y)
    (hw : F.leftIntermediateImageMap G H (F.tripleIncidenceToLeftSupportProduct G H w) =
      V.2.fromSpec p)
    (hgen : w ∈ genericPoints (F.tripleIncidence G H))
    (s : List ((pullback h h).presheaf.stalk (F.leftImageMiddlePair G H (V.2.fromSpec p))))
    (hs : IsRegular ((pullback h h).presheaf.stalk (F.leftImageMiddlePair G H (V.2.fromSpec p))) s)
    (hker : (pullback.diagonal h).ker.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s) :
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
      F.firstStageSourceRemainingEuler G H V p s y hy hp hker ⟨_, hw⟩ n) =
      F.tripleIncidenceTorCoefficient G H ⟨w, hgen⟩ := by
  classical
  obtain ⟨t, ht, hkt⟩ := F.exists_firstStageTripleFirstMiddleList G H w
  let t' : List (F.tripleIncidenceAmbientStalk G H w) :=
    t.map ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap
    (F.tripleIncidenceSixfoldInclusion G H w)).hom
  let s' : List (F.tripleIncidenceAmbientStalk G H w) :=
    (F.firstStageFiberTripleMiddleList G H (V.2.fromSpec p) w hw s).map
    ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap
      (F.tripleIncidenceSixfoldInclusion G H w)).hom
  let K := Koszul.coefficientComplex (F.tripleIncidenceSupportStalkModule G H w) t'
  have ht' : IsRegular (F.tripleIncidenceAmbientStalk G H w) t' :=
    (common_middle_diagonalLists_isRegular f g h i
      (F.tripleIncidenceFourfoldInclusion G H w) t
      (F.firstStageFiberTripleMiddleList G H (V.2.fromSpec p) w hw s)
      ht.toIsWeaklyRegular
      (F.firstStageFiberTripleMiddleList_isRegular G H (V.2.fromSpec p) w hw s hs).toIsWeaklyRegular
      hkt (F.firstStageFiberTripleMiddleList_ambient_kernel G H (V.2.fromSpec p) w hw s hker)).1
  let C := fun n => F.firstStageSourceRemainingKoszul G H V p s ⟨_, hw⟩ n
  let D := fun n => Koszul.coefficientComplex (K.homology n) s'
  have hC (n : ℕ) : LengthEuler.FiniteHomology (C n) :=
    F.firstStageSourceRemaining_finiteHomology G H V p s n
      (F.firstStageWholeRemaining_finiteHomology G H V p y hy hp s hker n) ⟨_, hw⟩
  have hlen (n r : ℕ) : Module.length _ ((C n).homology r) =
      Module.length _ ((D n).homology r) :=
    F.firstStageSourceCanonicalRemaining_length G H (V.2.fromSpec p) w hw s t' hkt ht' n r
  have hD (n : ℕ) : LengthEuler.FiniteHomology (D n) :=
    finiteHomology_of_source_lengths (hC n) (hlen n)
  have hE (n : ℕ) :
      F.firstStageSourceRemainingEuler G H V p s y hy hp hker ⟨_, hw⟩ n =
        LengthEuler.chainEuler (D n) (hD n) :=
    source_chainEuler_eq_of_lengths (hlen n) (hC n) (hD n)
  have hK (n : ℕ) (hn : t'.length < n) : K.ExactAt n :=
    HomologicalComplex.ExactAt.of_isZero
      (Koszul.coefficient_isZero_X (F.tripleIncidenceSupportStalkModule G H w) t' n hn)
  obtain ⟨hTotal, hTotalEuler⟩ := Koszul.bounded_koszulTensor_chainEuler K s' t'.length hK
    (fun n _ => hD n)
  obtain ⟨hCanonical, _, hCanonicalEuler⟩ := F.triple_common_total_coefficient G H ⟨w, hgen⟩ t
    (F.firstStageFiberTripleMiddleList G H (V.2.fromSpec p) w hw s) ht.toIsWeaklyRegular
    (F.firstStageFiberTripleMiddleList_isRegular G H (V.2.fromSpec p) w hw s hs).toIsWeaklyRegular
    hkt (F.firstStageFiberTripleMiddleList_ambient_kernel G H (V.2.fromSpec p) w hw s hker)
  have hzero (n : ℕ) (hn : t'.length < n) : LengthEuler.chainEuler (D n) (hD n) = 0 := by
    have : Subsingleton (K.homology n) := ModuleCat.subsingleton_of_isZero (hK n hn).isZero_homology
    exact Koszul.koszulDimension_chainEuler_zero_of_subsingleton (K.homology n) s' (hD n)
  calc
    _ = ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * LengthEuler.chainEuler (D n) (hD n) := by
      apply finsum_congr
      intro n
      rw [hE]
    _ = ∑ n ∈ Finset.range (t'.length + 1),
        (-1 : ℤ) ^ n * LengthEuler.chainEuler (D n) (hD n) := by
      apply finsum_eq_sum_of_support_subset
      intro n hn
      apply Finset.mem_range.mpr
      by_contra h
      exact hn (by
        change (-1 : ℤ) ^ n * LengthEuler.chainEuler (D n) (hD n) = 0
        rw [hzero n (by omega), mul_zero])
    _ = ∑ n : Fin (t'.length + 1),
        (-1 : ℤ) ^ (n : ℕ) * LengthEuler.chainEuler (D n) (hD n) := by
      exact (Fin.sum_univ_eq_sum_range _ _).symm
    _ = LengthEuler.chainEuler (HomologicalComplex.tensorObj (Koszul.chainComplex s') K)
        hTotal := hTotalEuler.symm
    _ = _ := hCanonicalEuler.symm


omit z w hw in
/-- Every point of the entire original finite fiber acquires its genuine generic
triple-incidence lift, and its full supported-Tor Euler sum is the canonical
coefficient of that lift. Genericity and the lift are derived from geometry. -/
theorem firstStageSourceRemainingEuler_exists_tripleLift
    [S.IsSeparated] [IsSeparated f] [IsSeparated g] [IsSeparated h] [IsSeparated i]
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [LocallyOfFiniteType i]
    [Flat f] [Smooth g] [Smooth h] [Flat i]
    [IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i)]
    (V : (F.leftIntermediateImageProduct G H).affineOpens)
    (p : Spec Γ(F.leftIntermediateImageProduct G H, V))
    [IsNoetherianRing ((F.leftIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p))]
    (y : F.leftImageIncidence G H) (hy : y ∈ genericPoints (F.leftImageIncidence G H))
    (hp : V.2.fromSpec p = F.leftImageIncidenceInclusion G H y)
    (s : List ((pullback h h).presheaf.stalk (F.leftImageMiddlePair G H (V.2.fromSpec p))))
    (hs : IsRegular ((pullback h h).presheaf.stalk (F.leftImageMiddlePair G H (V.2.fromSpec p))) s)
    (hker : (pullback.diagonal h).ker.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s)
    (x : {v : F.leftIntermediateSupportProduct G H //
      F.leftIntermediateImageMap G H v = V.2.fromSpec p}) :
    ∃ q : genericPoints (F.tripleIncidence G H),
      F.tripleIncidenceToLeftSupportProduct G H q.1 = x.1 ∧
      (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
        F.firstStageSourceRemainingEuler G H V p s y hy hp hker x n) =
        F.tripleIncidenceTorCoefficient G H q := by
  rcases x with ⟨x, hx⟩
  obtain ⟨w, hgen, _, hwx⟩ := F.leftImageIncidenceFiber_lift_generic G H y hy x (hx.trans hp)
  subst x
  exact ⟨⟨w, hgen⟩, rfl,
    F.firstStageSourceRemainingEuler_eq_tripleCoefficient G H w V p y hy hp hx hgen s hs hker⟩

omit z w hw in
/-- The actual finite pushforward outer sum is the residue-weighted canonical
triple coefficient on every branch of its original fiber. This attaches the
source side of the projection to the true total before any cycle replacement. -/
theorem firstStageRemainingProjection_to_tripleCoefficient
    [S.IsSeparated] [IsSeparated f] [IsSeparated g] [IsSeparated h] [IsSeparated i]
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [LocallyOfFiniteType i]
    [Flat f] [Smooth g] [Smooth h] [Flat i]
    [IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i)]
    (V : (F.leftIntermediateImageProduct G H).affineOpens)
    (p : Spec Γ(F.leftIntermediateImageProduct G H, V))
    [IsNoetherianRing ((F.leftIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p))]
    (y : F.leftImageIncidence G H) (hy : y ∈ genericPoints (F.leftImageIncidence G H))
    (hp : V.2.fromSpec p = F.leftImageIncidenceInclusion G H y)
    (s : List ((pullback h h).presheaf.stalk (F.leftImageMiddlePair G H (V.2.fromSpec p))))
    (hs : IsRegular ((pullback h h).presheaf.stalk (F.leftImageMiddlePair G H (V.2.fromSpec p))) s)
    (hker : (pullback.diagonal h).ker.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s) :
    ∃ lift : {v : F.leftIntermediateSupportProduct G H //
        F.leftIntermediateImageMap G H v = V.2.fromSpec p} →
        genericPoints (F.tripleIncidence G H),
      (∀ x, F.tripleIncidenceToLeftSupportProduct G H (lift x).1 = x.1) ∧
      (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
        F.firstStagePushforwardRemainingEuler G H V p s y hy hp hker n) =
      ∑ᶠ x : {v : F.leftIntermediateSupportProduct G H //
        F.leftIntermediateImageMap G H v = V.2.fromSpec p},
        ((F.leftIntermediateImageMap G H).residueDegree x.1 : ℤ) *
          F.tripleIncidenceTorCoefficient G H (lift x) := by
  classical
  choose lift hlift hEuler using
    F.firstStageSourceRemainingEuler_exists_tripleLift G H V p y hy hp s hs hker
  refine ⟨lift, hlift, (F.firstStageRemainingOuterProjectionEuler G H V p s y hy hp hker).trans ?_⟩
  apply finsum_congr
  intro x
  rw [hEuler x]

end Motivic.FiniteCorrespondenceGenerator
