/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Exterior.RightImage.ComponentGeometry
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.ExteriorImageRemainingTorAttachment
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.RightWholeFiberTorTargetReplacement

/-!
# The right full exterior quotient Euler and original remaining incidence Tor

At a genuine generic point of F.incidence P, the original remaining Y-diagonal
list is transported to the original four-factor ambient stalk. Its given
regularity and literal diagonal-kernel presentation survive only the actual
flat middle-pair base change. The coefficient exterior is not assumed flat.

The original image-product quotient by the exterior immersion's ideal-sheaf
stalk is identified linearly with the full exterior stalk. Three surjective
scalar maps compare Koszul lengths: the exterior immersion, the actual exterior
isomorphism, and the original ambient coefficient map. They use the same list
through the proved scalar square. Actual generic-incidence Tor supplies finite
length support and the final integer coefficient, including higher Tor.

The fixed-point theorem retains a list chosen at a given image-side point.
Its equality with the actual right exterior image point is proved from the original
remaining-incidence square and then eliminated, rather than assumed as an
unproved equality of Euler characteristics. No lift-existence, off-image, global
cycle, or right-bracket statement is claimed. The base field is arbitrary and
no connectedness or reducedness of the exterior is assumed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingTheory.Sequence

universe u

namespace Motivic.RightExteriorImageRemainingTorAttachment
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Products

open RightExteriorImageComponentGeometry _root_.HomologicalComplex.ModuleLengthEuler
open _root_.AlgebraicGeometry.Scheme.Hom (closedStalkQuotientLinearEquiv)
open _root_.Motivic.ExteriorImageRemainingTorAttachment (coefficientPointIso)

private def regularModuleIso {R T : Type u} [CommRing R] [CommRing T]
    (e : R ≃+* T) :
    ModuleCat.of R R ≅ (ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of T T) := by
  let l : ModuleCat.of R R ≃ₗ[R]
      (ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of T T) :=
    { e.toAddEquiv with map_smul' := fun r x => e.map_mul r x }
  exact l.toModuleIso

private theorem finiteHomology_of_lengths {R T : Type u} [CommRing R] [CommRing T]
    {K : ChainComplex (ModuleCat.{u} R) ℕ} {L : ChainComplex (ModuleCat.{u} T) ℕ}
    (hL : FiniteHomology L)
    (h : ∀ n, Module.length R (K.homology n) = Module.length T (L.homology n)) :
    FiniteHomology K where
  finite_length n := by rw [h n]; exact hL.finite_length n
  finite_support := by
    simpa only [show (fun n => Module.length R (K.homology n)) =
      (fun n => Module.length T (L.homology n)) from funext h] using hL.finite_support

private theorem chainEuler_eq_of_lengths {R T : Type u} [CommRing R] [CommRing T]
    {K : ChainComplex (ModuleCat.{u} R) ℕ} {L : ChainComplex (ModuleCat.{u} T) ℕ}
    (h : ∀ n, Module.length R (K.homology n) = Module.length T (L.homology n))
    (hK : FiniteHomology K) (hL : FiniteHomology L) :
    chainEuler K hK = chainEuler L hL := by
  unfold chainEuler homologyEuler signedLengthSum
  apply finsum_congr
  intro n
  simp only [integerLength, h n]

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)
  (C : IntegralClosedSubscheme (G.incidenceMap H).image)
  (P : FiniteCorrespondenceGenerator Y.hom W.hom)
  (hC : (C.val.subschemeι ≫ (G.incidenceMap H).imageι).ker = P.val)
  (w : F.incidence P)

local instance structureBaseNoetherian :
    IsLocallyNoetherian ((Functor.fromPUnit (Spec (.of k))).obj X.right) :=
  inferInstanceAs (IsLocallyNoetherian (Spec (.of k)))

local instance sourceLocallyNoetherian : IsLocallyNoetherian ((𝟭 Scheme).obj X.left) :=
  inferInstanceAs (IsLocallyNoetherian X.left)

local instance imageBaseNoetherian :
    IsNoetherian (pullback (F.targetProjection ≫ Y.hom) Y.hom) := by
  let : IsNoetherian ((𝟭 Scheme).obj X.left) := inferInstanceAs (IsNoetherian X.left)
  let : IsNoetherian F.scheme := isNoetherian_of_finiteType F.projection
  exact isNoetherian_of_finiteType (pullback.fst (F.targetProjection ≫ Y.hom) Y.hom)

local instance imageProjectionFinite : IsFinite (F.rightExteriorImageSourceMap G H) :=
  F.isFinite_rightExteriorImageSourceMap k G H

local instance imageProductNoetherian : IsNoetherian (F.rightIntermediateImageProduct G H) :=
  isNoetherian_of_finiteType (F.rightExteriorImageSourceMap G H)

local instance intersectionAmbientNoetherian :
    IsLocallyNoetherian (correspondenceIntersectionAmbient X.hom Y.hom W.hom) :=
  isLocallyNoetherian_correspondenceIntersectionAmbient X.hom Y.hom W.hom

local instance incidenceNoetherian : IsLocallyNoetherian (F.incidence P) :=
  F.isLocallyNoetherian_incidence P

/-- The literal immersion ideal-sheaf quotient has the actual exterior stalk's
original image-product module action; the full nonreduced stalk is retained. -/
def remainingExteriorQuotientLinearEquiv :
    ModuleCat.of
        ((F.rightIntermediateImageProduct G H).presheaf.stalk
          (F.rightImageComponentExteriorInclusion G H C (remainingToExterior F G H C P hC w)))
        (((F.rightIntermediateImageProduct G H).presheaf.stalk
          (F.rightImageComponentExteriorInclusion G H C (remainingToExterior F G H C P hC w))) ⧸
            (F.rightImageComponentExteriorInclusion G H C).ker.stalk
              (F.rightImageComponentExteriorInclusion G H C
                (remainingToExterior F G H C P hC w))) ≃ₗ[
        (F.rightIntermediateImageProduct G H).presheaf.stalk
          (F.rightImageComponentExteriorInclusion G H C (remainingToExterior F G H C P hC w))]
      (ModuleCat.restrictScalars
        ((F.rightImageComponentExteriorInclusion G H C).stalkMap
          (remainingToExterior F G H C P hC w)).hom).obj
        (ModuleCat.of ((F.rightImageComponentExterior G H C).presheaf.stalk
          (remainingToExterior F G H C P hC w))
          ((F.rightImageComponentExterior G H C).presheaf.stalk
            (remainingToExterior F G H C P hC w))) :=
  closedStalkQuotientLinearEquiv (F.rightImageComponentExteriorInclusion G H C)
    (remainingToExterior F G H C P hC w)

/-- Both regularity and the literal kernel presentation concern the image of
the same given middle list in the actual four-factor ambient stalk. -/
theorem remainingExteriorAmbientList_regular_kernel
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (F.rightImageMiddlePair G H
        (F.rightImageComponentExteriorInclusion G H C (remainingToExterior F G H C P hC w)))))
    (hsreg : IsRegular ((pullback Y.hom Y.hom).presheaf.stalk
      (F.rightImageMiddlePair G H
        (F.rightImageComponentExteriorInclusion G H C (remainingToExterior F G H C P hC w)))) s)
    (hker : (pullback.diagonal Y.hom).ker.stalk
      (F.rightImageMiddlePair G H
        (F.rightImageComponentExteriorInclusion G H C
          (remainingToExterior F G H C P hC w))) = Ideal.ofList s) :
    IsRegular (F.incidenceAmbientStalk P w)
        (remainingExteriorAmbientList F G H C P hC w s) ∧
      RingHom.ker ((correspondenceTripleInclusion X.hom Y.hom W.hom).stalkMap
        (F.incidenceInclusion P w)).hom =
          Ideal.ofList (remainingExteriorAmbientList F G H C P hC w s) := by
  have hs := FiniteCorrespondenceGenerator.stalkCongr_regular
    (remainingExterior_middlePoint F G H C P hC w) s hsreg
  have hk := FiniteCorrespondenceGenerator.stalkCongr_kernel
    (pullback.diagonal Y.hom).ker (remainingExterior_middlePoint F G H C P hC w) s hker
  rw [(pullback.diagonal Y.hom).ker_stalk] at hk
  exact Diagonal.mapped_equations_regular_kernel
    (correspondenceTriple_isPullback X.hom Y.hom W.hom) (F.incidenceInclusion P w) hs hk

/-- The original coefficient module is obtained using the actual equality of
support-product points, rather than an unrelated identification of scalar rings. -/
def remainingExteriorCoefficientIso :
    (ModuleCat.restrictScalars
      (remainingExteriorCoefficientStalkMap F G H C P hC w).hom).obj
        (ModuleCat.of ((F.supportProduct P).presheaf.stalk
          ((exteriorIso F G H C P hC).hom (remainingToExterior F G H C P hC w)))
          ((F.supportProduct P).presheaf.stalk
            ((exteriorIso F G H C P hC).hom (remainingToExterior F G H C P hC w)))) ≅
      F.incidenceSupportStalkModule P w :=
  coefficientPointIso (correspondenceTripleInclusion X.hom Y.hom W.hom)
    (F.incidenceInclusion P w) (F.supportProductInclusion P) _ _
    (remainingExterior_supportPoint F G H C P hC w)
    (remainingExterior_ambientPoint F G H C P hC w)
    (Intersection.point_eq _ _ _ _ (F.incidence_ambient_isPullback P) w)

/-- All three scalar restrictions use the original geometric maps. Their
surjectivity follows from the actual closed immersion, actual exterior
isomorphism, and original ambient coefficient closed immersion. -/
theorem remainingExterior_scalarMaps_surjective :
    Function.Surjective
        ((F.rightImageComponentExteriorInclusion G H C).stalkMap
          (remainingToExterior F G H C P hC w)).hom ∧
      Function.Surjective
        ((exteriorIso F G H C P hC).hom.stalkMap
          (remainingToExterior F G H C P hC w)).hom ∧
      Function.Surjective (remainingExteriorCoefficientStalkMap F G H C P hC w).hom := by
  refine ⟨(F.rightImageComponentExteriorInclusion G H C).stalkMap_surjective _, ?_, ?_⟩
  · exact (asIso ((exteriorIso F G H C P hC).hom.stalkMap
      (remainingToExterior F G H C P hC w))).commRingCatIsoToRingEquiv.surjective
  · exact Intersection.coefficientStalkMap_surjective
      (correspondenceTripleInclusion X.hom Y.hom W.hom) (F.incidenceInclusion P w)
      (F.supportProductInclusion P) _ (remainingExterior_ambientPoint F G H C P hC w)

/-- The three actual surjective scalar maps preserve every Koszul homology
length. The same original remaining list is retained through their proved square. -/
theorem remainingExterior_restricted_length
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (F.rightImageMiddlePair G H
        (F.rightImageComponentExteriorInclusion G H C
          (remainingToExterior F G H C P hC w))))) (n : ℕ) :
    Module.length
      ((F.rightIntermediateImageProduct G H).presheaf.stalk
        (F.rightImageComponentExteriorInclusion G H C (remainingToExterior F G H C P hC w)))
      ((_root_.ChainComplex.Koszul.coefficientComplex
        ((ModuleCat.restrictScalars
          ((F.rightImageComponentExteriorInclusion G H C).stalkMap
            (remainingToExterior F G H C P hC w)).hom).obj
          (ModuleCat.of ((F.rightImageComponentExterior G H C).presheaf.stalk
            (remainingToExterior F G H C P hC w))
            ((F.rightImageComponentExterior G H C).presheaf.stalk
              (remainingToExterior F G H C P hC w))))
        (F.rightTargetRemainingList G H
          (F.rightImageComponentExteriorInclusion G H C
            (remainingToExterior F G H C P hC w)) s)).homology n) =
      Module.length (F.incidenceAmbientStalk P w)
        ((_root_.ChainComplex.Koszul.coefficientComplex (F.incidenceSupportStalkModule P w)
          (remainingExteriorAmbientList F G H C P hC w s)).homology n) := by
  let e := remainingToExterior F G H C P hC w
  let j := F.rightImageComponentExteriorInclusion G H C
  let D := (F.rightImageComponentExterior G H C).presheaf.stalk e
  let B := (F.supportProduct P).presheaf.stalk ((exteriorIso F G H C P hC).hom e)
  let l := (j.stalkMap e).hom
  let ε := (exteriorIso F G H C P hC).hom.stalkMap e
  let a := (remainingExteriorCoefficientStalkMap F G H C P hC w).hom
  let t := F.rightTargetRemainingList G H (j e) s
  let r := remainingExteriorAmbientList F G H C P hC w s
  let MD := ModuleCat.of D D
  let MB := ModuleCat.of B B
  let eB : MB ≅ (ModuleCat.restrictScalars ε.hom).obj MD :=
    regularModuleIso (asIso ε).commRingCatIsoToRingEquiv
  have hsurj := remainingExterior_scalarMaps_surjective F G H C P hC w
  calc
    _ = Module.length D ((_root_.ChainComplex.Koszul.coefficientComplex MD (t.map l)).homology n) :=
      _root_.ChainComplex.Koszul.coefficientRestrict_length l hsurj.1 MD t n
    _ = Module.length D
        ((_root_.ChainComplex.Koszul.coefficientComplex MD ((r.map a).map ε.hom)).homology n) :=
      congrArg (fun q : List D => Module.length D ((_root_.ChainComplex.Koszul.coefficientComplex MD
          q).homology n))
        (remainingExterior_list_scalar_identity F G H C P hC w s)
    _ = Module.length B
        ((_root_.ChainComplex.Koszul.coefficientComplex ((ModuleCat.restrictScalars ε.hom).obj MD)
          (r.map a)).homology n) :=
      (_root_.ChainComplex.Koszul.coefficientRestrict_length ε.hom hsurj.2.1 MD (r.map a) n).symm
    _ = Module.length B ((_root_.ChainComplex.Koszul.coefficientComplex MB (r.map a)).homology n) :=
      ((HomologicalComplex.homologyFunctor _ _ n).mapIso
        (_root_.ChainComplex.Koszul.coefficientIso eB (r.map a))).toLinearEquiv.length_eq.symm
    _ = Module.length (F.incidenceAmbientStalk P w)
        ((_root_.ChainComplex.Koszul.coefficientComplex ((ModuleCat.restrictScalars a).obj MB)
            r).homology n) :=
      (_root_.ChainComplex.Koszul.coefficientRestrict_length a hsurj.2.2 MB r n).symm
    _ = _ :=
      ((HomologicalComplex.homologyFunctor _ _ n).mapIso
        (_root_.ChainComplex.Koszul.coefficientIso
          (remainingExteriorCoefficientIso F G H C P hC w) r)).toLinearEquiv.length_eq

omit w in
/-- The actual quotient-chain Euler equals the original generic-incidence Tor
coefficient. Both original regularity and literal diagonal generation are explicit. -/
theorem remainingQuotientEuler_eq_incidenceTorCoefficient
    (w : genericPoints (F.incidence P))
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (F.rightImageMiddlePair G H
        (F.rightImageComponentExteriorInclusion G H C (remainingToExterior F G H C P hC w.1)))))
    (hsreg : IsRegular ((pullback Y.hom Y.hom).presheaf.stalk
      (F.rightImageMiddlePair G H
        (F.rightImageComponentExteriorInclusion G H C (remainingToExterior F G H C P hC w.1)))) s)
    (hker : (pullback.diagonal Y.hom).ker.stalk
      (F.rightImageMiddlePair G H
        (F.rightImageComponentExteriorInclusion G H C
          (remainingToExterior F G H C P hC w.1))) = Ideal.ofList s) :
    let e := remainingToExterior F G H C P hC w.1
    let z := F.rightImageComponentExteriorInclusion G H C e
    let y := remainingToImage F G H C P hC w.1
    letI := F.rightTargetRemainingList_support_isArtinian G H z y
      (remainingToImage_mem_genericPoints F G H C P hC w.1 w.2)
      (remainingExterior_imagePoint F G H C P hC w.1).symm s hker
    chainEuler (_root_.ChainComplex.Koszul.coefficientComplex
      (ModuleCat.of ((F.rightIntermediateImageProduct G H).presheaf.stalk z)
        (((F.rightIntermediateImageProduct G H).presheaf.stalk z) ⧸
          (F.rightImageComponentExteriorInclusion G H C).ker.stalk z))
      (F.rightTargetRemainingList G H z s))
      (_root_.ChainComplex.Koszul.finiteHomology_of_artinian_quotient_of_le_annihilator _ _ ⊥
          bot_le) =
      F.incidenceTorCoefficient P w := by
  let e := remainingToExterior F G H C P hC w.1
  let j := F.rightImageComponentExteriorInclusion G H C
  let z := j e
  let y := remainingToImage F G H C P hC w.1
  let := F.rightTargetRemainingList_support_isArtinian G H z y
    (remainingToImage_mem_genericPoints F G H C P hC w.1 w.2)
    (remainingExterior_imagePoint F G H C P hC w.1).symm s hker
  let R := (F.rightIntermediateImageProduct G H).presheaf.stalk z
  let Q := ModuleCat.of R (R ⧸ j.ker.stalk z)
  let D := (F.rightImageComponentExterior G H C).presheaf.stalk e
  let N := (ModuleCat.restrictScalars (j.stalkMap e).hom).obj (ModuleCat.of D D)
  let t := F.rightTargetRemainingList G H z s
  let r := remainingExteriorAmbientList F G H C P hC w.1 s
  let K := _root_.ChainComplex.Koszul.coefficientComplex (F.incidenceSupportStalkModule P w.1) r
  obtain ⟨hr, hk⟩ := remainingExteriorAmbientList_regular_kernel F G H C P hC w.1 s hsreg hker
  have hK : FiniteHomology K :=
    (F.incidenceTor_finiteLengthSupport P w.1 w.2).of_iso (fun n =>
      Intersection.torIsoHomology (correspondenceTripleInclusion X.hom Y.hom W.hom)
        (F.incidenceInclusion P w.1) (F.supportProductInclusion P)
        (F.incidenceToSupportProduct P w.1)
        (Intersection.point_eq _ _ _ _ (F.incidence_ambient_isPullback P) w.1) r hk hr n)
  have hlen := remainingExterior_restricted_length F G H C P hC w.1 s
  have hN : FiniteHomology (_root_.ChainComplex.Koszul.coefficientComplex N t) :=
    finiteHomology_of_lengths hK hlen
  have hQ : FiniteHomology (_root_.ChainComplex.Koszul.coefficientComplex Q t) :=
    _root_.ChainComplex.Koszul.finiteHomology_of_artinian_quotient_of_le_annihilator Q t ⊥ bot_le
  have htor : F.incidenceTorCoefficient P w = chainEuler K hK :=
    Intersection.torEuler_eq_chainEuler (F.incidenceInclusion P)
      (F.incidenceToSupportProduct P) (correspondenceTripleInclusion X.hom Y.hom W.hom)
      (F.supportProductInclusion P) (F.incidence_ambient_isPullback P) w.1 w.2 r hk hr
  exact (_root_.ChainComplex.Koszul.coefficient_chainEuler_eq_of_linearEquiv Q N
    (remainingExteriorQuotientLinearEquiv F G H C P hC w.1) t hQ hN).trans
      ((chainEuler_eq_of_lengths hlen hN hK).trans htor.symm)

omit w in
/-- A fixed image point and its original list are retained. The necessary
point transport follows from the actual remaining-incidence square. -/
theorem remainingQuotientEuler_eq_incidenceTorCoefficient_fixedPoint
    (w : genericPoints (F.incidence P))
    (x : F.rightIntermediateImageProduct G H)
    (y : F.rightImageIncidence G H) (hy : y ∈ genericPoints (F.rightImageIncidence G H))
    (hp : x = F.rightImageIncidenceInclusion G H y)
    (hwy : remainingToImage F G H C P hC w.1 = y)
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk (F.rightImageMiddlePair G H x)))
    (hsreg : IsRegular ((pullback Y.hom Y.hom).presheaf.stalk (F.rightImageMiddlePair G H x)) s)
    (hker : (pullback.diagonal Y.hom).ker.stalk (F.rightImageMiddlePair G H x) = Ideal.ofList s) :
    letI := F.rightTargetRemainingList_support_isArtinian G H x y hy hp s hker
    chainEuler (_root_.ChainComplex.Koszul.coefficientComplex
      (ModuleCat.of ((F.rightIntermediateImageProduct G H).presheaf.stalk x)
        (((F.rightIntermediateImageProduct G H).presheaf.stalk x) ⧸
          (F.rightImageComponentExteriorInclusion G H C).ker.stalk x))
      (F.rightTargetRemainingList G H x s))
      (_root_.ChainComplex.Koszul.finiteHomology_of_artinian_quotient_of_le_annihilator _ _ ⊥
          bot_le) =
      F.incidenceTorCoefficient P w := by
  have hx : x = F.rightImageComponentExteriorInclusion G H C
    (remainingToExterior F G H C P hC w.1) :=
    hp.trans ((congrArg (F.rightImageIncidenceInclusion G H) hwy).symm.trans
      (remainingExterior_imagePoint F G H C P hC w.1))
  subst hx
  exact remainingQuotientEuler_eq_incidenceTorCoefficient F G H C P hC w s hsreg hker

end Motivic.RightExteriorImageRemainingTorAttachment
