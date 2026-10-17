/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.TripleFixedSupportTorComparison
public import Motivic.AlgebraicGeometry.Intersection.WholeFiberTorGeneric
public import Motivic.AlgebraicGeometry.Cycles.WholeFiberTorSourceTotal
public import Motivic.AlgebraicGeometry.Cycles.GenericStalkLocalization
public import Motivic.Algebra.Homology.KoszulExteriorCoefficientLocalization

/-!
# Original whole Tor stalks at the literal fixed-support generic primes

This leaf continues the frozen fixed-support sum packet.
It constructs the scalar-compatible comparisons needed to identify the local
homology weights with genuine whole-open Tor stalk coefficients. The accepted
fixed-support packet is not modified or made dependent on this continuation.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Motivic.LengthEuler
open scoped TensorProduct

universe u

namespace Motivic.Intersection

variable {D T P V : Scheme.{u}} (i : D ⟶ P) (j : T ⟶ P)
  [IsClosedImmersion i] [IsClosedImmersion j]
  (a : V ⟶ D) (b : V ⟶ T) (sq : IsPullback a b i j)

/-- The same genuine affine Tor module computes both supported stalks, so its
extension along the actual specialization map is the original specialized stalk. -/
def closedIntersectionSupportedStalkSpecializationIso (U : P.affineOpens)
    (x y : V) (hx : (a ≫ i) x ∈ U.1) (hyx : y ⤳ x) (n : ℕ) :
    (ModuleCat.extendScalars (V.presheaf.stalkSpecializes hyx).hom).obj
        (closedIntersectionSupportedStalkTor i j a b sq x n) ≅
      closedIntersectionSupportedStalkTor i j a b sq y n := by
  have hy : (a ≫ i) y ∈ U.1 := (hyx.map (a ≫ i).continuous).mem_open U.1.isOpen hx
  let M := closedIntersectionAffineTor j a b i sq U n
  let fx := (V.presheaf.germ ((a ≫ i) ⁻¹ᵁ U) x hx).hom
  let fy := (V.presheaf.germ ((a ≫ i) ⁻¹ᵁ U) y hy).hom
  let f := (V.presheaf.stalkSpecializes hyx).hom
  have hf : f.comp fx = fy := by
    exact congrArg CommRingCat.Hom.hom
      (V.presheaf.germ_stalkSpecializes hx hyx)
  exact (ModuleCat.extendScalars f).mapIso
      (closedIntersectionAffineTorStalkIso i j a b sq U x hx n).symm ≪≫
    (ModuleCat.extendScalarsComp fx f).symm.app M ≪≫
    eqToIso (congrArg (fun q => (ModuleCat.extendScalars q).obj M) hf) ≪≫
    closedIntersectionAffineTorStalkIso i j a b sq U y hy n

/-- Literal localization at the support generic prime recovers the original
supported generic stalk, with the canonical global-stalk localization action. -/
def closedIntersectionSupportedStalkGenericIso (U : P.affineOpens)
    (x : V) (hx : (a ≫ i) x ∈ U.1)
    (y : {y : genericPoints V // y.1 ⤳ x}) (n : ℕ) :
    ModuleCat.of (Localization.AtPrime (genericStalkLocalizationPrime V x y).asIdeal)
        (LocalizedModule (genericStalkLocalizationPrime V x y).asIdeal.primeCompl
          (closedIntersectionSupportedStalkTor i j a b sq x n)) ≅
      (ModuleCat.restrictScalars (genericStalkLocalizationIso V x y).inv.hom).obj
        (closedIntersectionSupportedStalkTor i j a b sq y.1.1 n) := by
  let M := closedIntersectionSupportedStalkTor i j a b sq x n
  let f := (V.presheaf.stalkSpecializes y.2).hom
  let e := (genericStalkLocalizationIso V x y).commRingCatIsoToRingEquiv
  have hf : e.toRingHom.comp f = algebraMap (V.presheaf.stalk x)
      (Localization.AtPrime (genericStalkLocalizationPrime V x y).asIdeal) :=
    congrArg CommRingCat.Hom.hom (stalkSpecializes_genericStalkLocalizationIso V x y)
  exact TorComparison.localizedModuleExtendScalarsIso _ M ≪≫
    eqToIso (congrArg (fun q => (ModuleCat.extendScalars q).obj M) hf.symm) ≪≫
    (ModuleCat.extendScalarsComp f e.toRingHom).app M ≪≫
    (ModuleCat.extendScalars e.toRingHom).mapIso
      (closedIntersectionSupportedStalkSpecializationIso i j a b sq U x y.1.1 hx y.2 n) ≪≫
    extendScalarsRingEquivIso e _

/-- The generic localization equality preserves actual lengths over the full
nonreduced generic stalk, with no replacement by a residue field. -/
theorem closedIntersectionSupportedStalkGeneric_length (U : P.affineOpens)
    (x : V) (hx : (a ≫ i) x ∈ U.1)
    (y : {y : genericPoints V // y.1 ⤳ x}) (n : ℕ) :
    Module.length (Localization.AtPrime (genericStalkLocalizationPrime V x y).asIdeal)
        (LocalizedModule (genericStalkLocalizationPrime V x y).asIdeal.primeCompl
          (closedIntersectionSupportedStalkTor i j a b sq x n)) =
      Module.length (V.presheaf.stalk y.1.1)
        (closedIntersectionSupportedStalkTor i j a b sq y.1.1 n) := by
  rw [(closedIntersectionSupportedStalkGenericIso i j a b sq U x hx y n).toLinearEquiv.length_eq]
  exact TorComparison.length_restrictScalars_of_surjective _
    (ConcreteCategory.bijective_of_isIso (genericStalkLocalizationIso V x y).inv).2 _

end Motivic.Intersection

namespace Motivic.TorComparison

/-- An actual surjective scalar map and scalar-compatible module isomorphism
preserve localized lengths at the literal contracted support prime. -/
theorem localizedLength_eq_of_surjectiveIso
    {R B : Type u} [CommRing R] [CommRing B]
    (f : R →+* B) (hf : Function.Surjective f)
    (p : Ideal R) [p.IsPrime] (q : Ideal B) [q.IsPrime] (hpq : p = q.comap f)
    (M : ModuleCat.{u} R) (N : ModuleCat.{u} B)
    (e : M ≅ (ModuleCat.restrictScalars f).obj N) :
    Module.length (Localization.AtPrime p) (Localization.AtPrime p ⊗[R] M) =
      Module.length (Localization.AtPrime q) (LocalizedModule q.primeCompl N) := by
  let e' := Koszul.primeLocalizedModuleMapIso p e ≪≫
    surjectivePrimeLocalizedModuleIso f hf p q hpq N
  exact (LocalizedModule.equivTensorProduct p.primeCompl M).length_eq.symm.trans
    (e'.toLinearEquiv.length_eq.trans
      (length_restrictScalars_of_surjective _ (localRingHom_surjective f hf p q hpq) _))

end Motivic.TorComparison

namespace Motivic.FiniteCorrespondenceGenerator

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i) [IsSeparated g]

/-- The first-list homology at the original triple point is the genuine
supported first-stage Tor, with its actual equality-aligned ambient action. -/
def tripleFirstStageHomologySupportedIso (w : F.tripleIncidence G H)
    (t : List (F.tripleIncidenceAmbientStalk G H w))
    (ht : (correspondenceFirstDiagonalInclusion f g h i).ker.stalk
      (F.tripleIncidenceSixfoldInclusion G H w) = Ideal.ofList t)
    (hr : RingTheory.Sequence.IsRegular (F.tripleIncidenceAmbientStalk G H w) t) (n : ℕ) :
    (Koszul.coefficientComplex (F.tripleIncidenceSupportStalkModule G H w) t).homology n ≅
      (ModuleCat.restrictScalars (F.tripleFirstStageStalkMap G H w).hom).obj
        (Intersection.closedIntersectionSupportedStalkTor
          (correspondenceFirstDiagonalInclusion f g h i) (F.tripleSupportProductInclusion G H)
          (F.leftIntermediateSupportInclusion G H) (F.leftIntermediateToTripleSupport G H)
          (F.leftIntermediate_ambient_isPullback G H)
          (F.tripleIncidenceToLeftSupportProduct G H w) n) := by
  let e := F.firstStageTripleAmbientStalkIso G H w
  let M := (Koszul.coefficientComplex (F.tripleIncidenceSupportStalkModule G H w) t).homology n
  let N := F.firstStageSupportedStalkTor G H (F.tripleIncidenceToLeftSupportProduct G H w) n
  let f₀ := ((F.leftIntermediateAmbientInclusion G H).stalkMap
    (F.tripleIncidenceToLeftSupportProduct G H w)).hom
  have hf : f₀.comp e.inv.hom = (F.tripleFirstStageStalkMap G H w).hom := rfl
  exact (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      e.commRingCatIsoToRingEquiv).unitIso.app M ≪≫
    (ModuleCat.restrictScalars e.inv.hom).mapIso
      (F.firstStageSupportedCanonicalHomologyIso G H w t ht hr n).symm ≪≫
    (ModuleCat.restrictScalarsComp e.inv.hom f₀).symm.app N ≪≫
    (ModuleCat.restrictScalarsCongr hf).app N

/-- The actual localized first-list homology length equals the genuine global
supported generic Tor stalk length at the exact source-generic index. -/
theorem tripleFirstStageGeneric_localized_length (w : F.tripleIncidence G H)
    (t : List (F.tripleIncidenceAmbientStalk G H w))
    (ht : (correspondenceFirstDiagonalInclusion f g h i).ker.stalk
      (F.tripleIncidenceSixfoldInclusion G H w) = Ideal.ofList t)
    (hr : RingTheory.Sequence.IsRegular (F.tripleIncidenceAmbientStalk G H w) t)
    (y : {y : genericPoints (F.leftIntermediateSupportProduct G H) //
      y.1 ⤳ F.tripleIncidenceToLeftSupportProduct G H w})
    (U : (correspondenceSixfoldAmbient f g h i).affineOpens)
    (hU : F.leftIntermediateAmbientInclusion G H
      (F.tripleIncidenceToLeftSupportProduct G H w) ∈ U.1) (n : ℕ) :
    let p := (F.tripleFirstStageSupportGenericEquiv G H w t ht).symm y
    let : p.1.IsPrime := p.2.isPrime
    Module.length (Localization.AtPrime p.1)
        (Localization.AtPrime p.1 ⊗[F.tripleIncidenceAmbientStalk G H w]
          (Koszul.coefficientComplex (F.tripleIncidenceSupportStalkModule G H w) t).homology n) =
      Module.length ((F.leftIntermediateSupportProduct G H).presheaf.stalk y.1.1)
        (Intersection.closedIntersectionSupportedStalkTor
          (correspondenceFirstDiagonalInclusion f g h i) (F.tripleSupportProductInclusion G H)
          (F.leftIntermediateSupportInclusion G H) (F.leftIntermediateToTripleSupport G H)
          (F.leftIntermediate_ambient_isPullback G H) y.1.1 n) := by
  let p := (F.tripleFirstStageSupportGenericEquiv G H w t ht).symm y
  let : p.1.IsPrime := p.2.isPrime
  let q := genericStalkLocalizationPrime (F.leftIntermediateSupportProduct G H)
    (F.tripleIncidenceToLeftSupportProduct G H w) y
  have hpq : p.1 = q.asIdeal.comap (F.tripleFirstStageStalkMap G H w).hom :=
    F.tripleFirstStageSupportGenericEquiv_symm_val G H w t ht y
  exact (TorComparison.localizedLength_eq_of_surjectiveIso
    (F.tripleFirstStageStalkMap G H w).hom (F.tripleFirstStageStalkMap_surjective G H w)
    p.1 q.asIdeal hpq _ _ (F.tripleFirstStageHomologySupportedIso G H w t ht hr n)).trans
      (Intersection.closedIntersectionSupportedStalkGeneric_length
        (correspondenceFirstDiagonalInclusion f g h i) (F.tripleSupportProductInclusion G H)
        (F.leftIntermediateSupportInclusion G H) (F.leftIntermediateToTripleSupport G H)
        (F.leftIntermediate_ambient_isPullback G H) U
        (F.tripleIncidenceToLeftSupportProduct G H w) hU y n)

end Motivic.FiniteCorrespondenceGenerator

namespace Motivic.FiniteCorrespondenceGenerator

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)
  (V : (F.leftIntermediateImageProduct G H).affineOpens)

local instance : (correspondenceSixfoldAmbient X.hom Y.hom Z.hom W.hom).IsSeparated :=
  correspondenceSixfoldAmbient_isSeparated (S := Spec (.of k)) X.hom Y.hom Z.hom W.hom

local instance : IsLocallyNoetherian
    (correspondenceSixfoldAmbient X.hom Y.hom Z.hom W.hom) :=
  isLocallyNoetherian_correspondenceSixfoldAmbient (S := Spec (.of k))
    X.hom Y.hom Z.hom W.hom

/-- Every original support generic specializing to a point of the whole open
belongs to that same whole open. It retains the identical original source point. -/
def tripleFirstStageWholeGeneric (w : F.tripleIncidence G H)
    (hV : F.tripleIncidenceToLeftSupportProduct G H w ∈
      (F.leftIntermediateImageMap G H) ⁻¹ᵁ V)
    (y : {y : genericPoints (F.leftIntermediateSupportProduct G H) //
      y.1 ⤳ F.tripleIncidenceToLeftSupportProduct G H w}) :
    genericPoints (F.firstStageWholeOpen G H V) := by
  let z : F.firstStageWholeOpen G H V :=
    ⟨y.1.1, y.2.mem_open ((F.leftIntermediateImageMap G H) ⁻¹ᵁ V).isOpen hV⟩
  exact ⟨z, mem_genericPoints_of_preimmersion_image
    ((F.leftIntermediateImageMap G H) ⁻¹ᵁ V).ι z y.1.2⟩

/-- Passing through the whole open has not changed the source generic index. -/
theorem firstStageWholeGenericOriginal_tripleFirstStageWholeGeneric
    (w : F.tripleIncidence G H)
    (hV : F.tripleIncidenceToLeftSupportProduct G H w ∈
      (F.leftIntermediateImageMap G H) ⁻¹ᵁ V)
    (y : {y : genericPoints (F.leftIntermediateSupportProduct G H) //
      y.1 ⤳ F.tripleIncidenceToLeftSupportProduct G H w}) :
    F.firstStageWholeGenericOriginal G H V (F.tripleFirstStageWholeGeneric G H V w hV y) =
      y.1 := rfl

/-- The fixed-support local homology length is the original whole Tor sheaf's
actual generic stalk length. The support prime and ambient action are literal. -/
theorem tripleFirstStageWholeGeneric_localized_length (w : F.tripleIncidence G H)
    (hV : F.tripleIncidenceToLeftSupportProduct G H w ∈
      (F.leftIntermediateImageMap G H) ⁻¹ᵁ V)
    (t : List (F.tripleIncidenceAmbientStalk G H w))
    (ht : (correspondenceFirstDiagonalInclusion X.hom Y.hom Z.hom W.hom).ker.stalk
      (F.tripleIncidenceSixfoldInclusion G H w) = Ideal.ofList t)
    (hr : RingTheory.Sequence.IsRegular (F.tripleIncidenceAmbientStalk G H w) t)
    (y : {y : genericPoints (F.leftIntermediateSupportProduct G H) //
      y.1 ⤳ F.tripleIncidenceToLeftSupportProduct G H w}) (n : ℕ) :
    let p := (F.tripleFirstStageSupportGenericEquiv G H w t ht).symm y
    let : p.1.IsPrime := p.2.isPrime
    Module.length (Localization.AtPrime p.1)
        (Localization.AtPrime p.1 ⊗[F.tripleIncidenceAmbientStalk G H w]
          (Koszul.coefficientComplex (F.tripleIncidenceSupportStalkModule G H w) t).homology n) =
      Module.length ((F.firstStageWholeOpen G H V).presheaf.stalk
        (F.tripleFirstStageWholeGeneric G H V w hV y).1)
        (F.firstStageWholeGenericStalk G H V
          (F.tripleFirstStageWholeGeneric G H V w hV y) n) := by
  obtain ⟨r, hr'⟩ := Intersection.wholeFiberTorCoefficient_chart_at
    (F.tripleSupportProductInclusion G H)
    (correspondenceFirstDiagonalInclusion X.hom Y.hom Z.hom W.hom)
    (F.leftIntermediateSupportInclusion G H) (F.leftIntermediateToTripleSupport G H)
    (F.leftIntermediate_ambient_isPullback G H) (F.leftIntermediateImageMap G H) V hV
  let U := Intersection.wholeFiberTorAmbientFamily (F.tripleSupportProductInclusion G H)
    (correspondenceFirstDiagonalInclusion X.hom Y.hom Z.hom W.hom)
    (F.leftIntermediateSupportInclusion G H) (F.leftIntermediateToTripleSupport G H)
    (F.leftIntermediate_ambient_isPullback G H) (F.leftIntermediateImageMap G H) V r
  let z := F.tripleFirstStageWholeGeneric G H V w hV y
  have he := (Intersection.wholeFiberTorCoefficientOriginalStalkIso
    (F.tripleSupportProductInclusion G H)
    (correspondenceFirstDiagonalInclusion X.hom Y.hom Z.hom W.hom)
    (F.leftIntermediateSupportInclusion G H) (F.leftIntermediateToTripleSupport G H)
    (F.leftIntermediate_ambient_isPullback G H) (F.leftIntermediateImageMap G H) V
    z.1 n).toLinearEquiv.length_eq
  rw [TorComparison.length_restrictScalars_of_surjective _
    (((F.leftIntermediateImageMap G H) ⁻¹ᵁ V).ι.stalkMap_surjective z.1)] at he
  exact (F.tripleFirstStageGeneric_localized_length G H w t ht hr y U hr' n).trans he.symm

/-- Every fixed-support generic weight equals the original whole sheaf's true
all-degree generic coefficient, after the proved length comparison and bound. -/
theorem twoListGenericEuler_eq_firstStageWholeTorGenericCoefficient
    (w : F.tripleIncidence G H)
    (hV : F.tripleIncidenceToLeftSupportProduct G H w ∈
      (F.leftIntermediateImageMap G H) ⁻¹ᵁ V)
    (t : List (F.tripleIncidenceAmbientStalk G H w))
    (ht : (correspondenceFirstDiagonalInclusion X.hom Y.hom Z.hom W.hom).ker.stalk
      (F.tripleIncidenceSixfoldInclusion G H w) = Ideal.ofList t)
    (hr : RingTheory.Sequence.IsRegular (F.tripleIncidenceAmbientStalk G H w) t)
    (y : {y : genericPoints (F.leftIntermediateSupportProduct G H) //
      y.1 ⤳ F.tripleIncidenceToLeftSupportProduct G H w}) :
    Koszul.twoListGenericEuler (F.tripleIncidenceSupportStalkModule G H w) t
        ((F.tripleFirstStageSupportGenericEquiv G H w t ht).symm y) =
      F.firstStageWholeTorGenericCoefficient G H V
        (F.tripleFirstStageWholeGeneric G H V w hV y) := by
  classical
  let M := F.tripleIncidenceSupportStalkModule G H w
  let p := (F.tripleFirstStageSupportGenericEquiv G H w t ht).symm y
  let : p.1.IsPrime := p.2.isPrime
  let z := F.tripleFirstStageWholeGeneric G H V w hV y
  have hlen := F.tripleFirstStageWholeGeneric_localized_length G H V w hV t ht hr y
  have hsupport : Function.support (fun n =>
      Module.length ((F.firstStageWholeOpen G H V).presheaf.stalk z.1)
        (F.firstStageWholeGenericStalk G H V z n)) ⊆
      (Finset.range (t.length + 1) : Set ℕ) := by
    intro n hn
    by_contra hnot
    have hbound : t.length < n := by simpa using hnot
    have : Subsingleton ((Koszul.coefficientComplex M t).homology n) :=
      ModuleCat.subsingleton_of_isZero
        (HomologicalComplex.ExactAt.of_isZero
          (Koszul.coefficient_isZero_X M t n hbound)).isZero_homology
    apply hn
    change Module.length ((F.firstStageWholeOpen G H V).presheaf.stalk z.1)
      (F.firstStageWholeGenericStalk G H V z n) = 0
    dsimp only [z]
    rw [← hlen n]
    exact Module.length_eq_zero
  unfold firstStageWholeTorGenericCoefficient
  rw [signedLengthSum_eq_sum _ _ _ (Finset.range (t.length + 1)) hsupport]
  rw [← Fin.sum_univ_eq_sum_range]
  unfold Koszul.twoListGenericEuler
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  simp only [Koszul.fixedSupportGenericLength, integerLength]
  rw [hlen n]

/-- The actual local weight retains the genuine pair Tor coefficient and the
original exterior closed-fiber multiplicity. No generic source/image bijection enters. -/
theorem twoListGenericEuler_eq_original_pair_mul
    (w : F.tripleIncidence G H)
    (hV : F.tripleIncidenceToLeftSupportProduct G H w ∈
      (F.leftIntermediateImageMap G H) ⁻¹ᵁ V)
    (t : List (F.tripleIncidenceAmbientStalk G H w))
    (ht : (correspondenceFirstDiagonalInclusion X.hom Y.hom Z.hom W.hom).ker.stalk
      (F.tripleIncidenceSixfoldInclusion G H w) = Ideal.ofList t)
    (hr : RingTheory.Sequence.IsRegular (F.tripleIncidenceAmbientStalk G H w) t)
    (y : {y : genericPoints (F.leftIntermediateSupportProduct G H) //
      y.1 ⤳ F.tripleIncidenceToLeftSupportProduct G H w}) :
    let z := F.tripleFirstStageWholeGeneric G H V w hV y
    Koszul.twoListGenericEuler (F.tripleIncidenceSupportStalkModule G H w) t
        ((F.tripleFirstStageSupportGenericEquiv G H w t ht).symm y) =
      F.incidenceTorCoefficient (S := Spec (.of k)) G (F.firstStageWholeGenericPair G H V z) *
        F.firstStageWholeGenericFiberMultiplicity G H V z :=
  (F.twoListGenericEuler_eq_firstStageWholeTorGenericCoefficient G H V w hV t ht hr y).trans
    (F.firstStageWholeTorGenericCoefficient_eq_pair_mul G H V _)

/-- The original whole-sheaf generic coefficients replace the actual local
first-list weights in the accepted source-generic sum for canonical triple Tor. -/
theorem triple_originalWholeTor_fixedSupport_sum_eq_coefficient
    (w : genericPoints (F.tripleIncidence G H))
    (hV : F.tripleIncidenceToLeftSupportProduct G H w.1 ∈
      (F.leftIntermediateImageMap G H) ⁻¹ᵁ V)
    (t s : List (F.tripleIncidenceAmbientStalk G H w.1))
    (ht : (correspondenceFirstDiagonalInclusion X.hom Y.hom Z.hom W.hom).ker.stalk
      (F.tripleIncidenceSixfoldInclusion G H w.1) = Ideal.ofList t)
    (hrt : RingTheory.Sequence.IsRegular (F.tripleIncidenceAmbientStalk G H w.1) t)
    (hr : RingTheory.Sequence.IsRegular (F.tripleIncidenceAmbientStalk G H w.1) (t ++ s))
    (hker : RingHom.ker
      ((correspondenceSecondDiagonalInclusion X.hom Y.hom Z.hom W.hom ≫
        correspondenceFirstDiagonalInclusion X.hom Y.hom Z.hom W.hom).stalkMap
          (F.tripleIncidenceFourfoldInclusion G H w.1)).hom = Ideal.ofList (t ++ s)) :
    let := F.tripleTwoList_support_isArtinian (S := Spec (.of k)) G H w t s hker
    let M := F.tripleIncidenceSupportStalkModule G H w.1
    (∑ᶠ y : {y : genericPoints (F.leftIntermediateSupportProduct G H) //
      y.1 ⤳ F.tripleIncidenceToLeftSupportProduct G H w.1},
      let p := (F.tripleFirstStageSupportGenericEquiv G H w.1 t ht).symm y
      F.firstStageWholeTorGenericCoefficient G H V
          (F.tripleFirstStageWholeGeneric G H V w.1 hV y) *
        chainEuler (Koszul.coefficientComplex
          (ModuleCat.of (F.tripleIncidenceAmbientStalk G H w.1)
            ((F.tripleIncidenceAmbientStalk G H w.1) ⧸ p.1)) s)
          (Koszul.fixedSupport_prime_finiteHomology s
            (Ideal.ofList t ⊔ Module.annihilator (F.tripleIncidenceAmbientStalk G H w.1) M)
            p.1 p.2.le)) = F.tripleIncidenceTorCoefficient (S := Spec (.of k)) G H w := by
  dsimp only
  let := F.tripleTwoList_support_isArtinian (S := Spec (.of k)) G H w t s hker
  refine Eq.trans ?_ (F.triple_geometric_fixedSupport_sum_eq_coefficient
    (S := Spec (.of k)) G H w t s ht hr hker)
  apply finsum_congr
  intro y
  congr 1
  exact (F.twoListGenericEuler_eq_firstStageWholeTorGenericCoefficient
    G H V w.1 hV t ht hrt y).symm

/-- The original smooth first diagonal constructs a regular list and its
literal support presentation before attaching every genuine generic weight. -/
theorem exists_firstStageWholeGeneric_attachment
    (w : F.tripleIncidence G H)
    (hV : F.tripleIncidenceToLeftSupportProduct G H w ∈
      (F.leftIntermediateImageMap G H) ⁻¹ᵁ V) :
    ∃ (t : List (F.tripleIncidenceAmbientStalk G H w))
      (ht : (correspondenceFirstDiagonalInclusion X.hom Y.hom Z.hom W.hom).ker.stalk
        (F.tripleIncidenceSixfoldInclusion G H w) = Ideal.ofList t),
      RingTheory.Sequence.IsRegular (F.tripleIncidenceAmbientStalk G H w) t ∧
        ∀ y : {y : genericPoints (F.leftIntermediateSupportProduct G H) //
          y.1 ⤳ F.tripleIncidenceToLeftSupportProduct G H w},
          Koszul.twoListGenericEuler (F.tripleIncidenceSupportStalkModule G H w) t
              ((F.tripleFirstStageSupportGenericEquiv G H w t ht).symm y) =
            F.firstStageWholeTorGenericCoefficient G H V
              (F.tripleFirstStageWholeGeneric G H V w hV y) := by
  obtain ⟨t, hr, hk⟩ := exists_regular_kernel_correspondenceFirstDiagonal
    X.hom Y.hom Z.hom W.hom
    (correspondenceSecondDiagonalInclusion X.hom Y.hom Z.hom W.hom
      (F.tripleIncidenceFourfoldInclusion G H w))
  have ht : (correspondenceFirstDiagonalInclusion X.hom Y.hom Z.hom W.hom).ker.stalk
      (F.tripleIncidenceSixfoldInclusion G H w) = Ideal.ofList t :=
    ((correspondenceFirstDiagonalInclusion X.hom Y.hom Z.hom W.hom).ker_stalk _).trans hk
  exact ⟨t, ht, hr, fun y =>
    F.twoListGenericEuler_eq_firstStageWholeTorGenericCoefficient G H V w hV t ht hr y⟩

end Motivic.FiniteCorrespondenceGenerator
