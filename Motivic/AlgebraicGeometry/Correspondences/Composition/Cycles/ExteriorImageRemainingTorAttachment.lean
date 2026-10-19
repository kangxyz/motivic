/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.IdealSheaf.Stalk.ClosedQuotientLinearEquiv

public import Motivic.AlgebraicGeometry.Correspondences.Exterior.Image.RemainingScalars
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.ExteriorImageComponentEulerReplacement
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.WholeFiberTorSourceTotal
public import Motivic.Aglib.Algebra.Homology.Koszul.ScalarRestriction.Length

/-!
# The full exterior quotient Euler and the original remaining incidence Tor

At a genuine generic point of the component incidence, the original middle
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
Its equality with the actual exterior image point is proved from the original
remaining-incidence square and then eliminated, rather than assumed as an
unproved equality of Euler characteristics. No global cycle identity is claimed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingTheory.Sequence

universe u

namespace Motivic.ExteriorImageRemainingTorAttachment
open _root_.Motivic.ExteriorImageComponentGeometry
open _root_.HomologicalComplex.ModuleLengthEuler
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Hom
open _root_.AlgebraicGeometry.Scheme.Products


private def regularModuleIso {R T : Type u} [CommRing R] [CommRing T]
    (e : R ≃+* T) :
    ModuleCat.of R R ≅ (ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of T T) := by
  let l : ModuleCat.of R R ≃ₗ[R]
      (ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of T T) :=
    { e.toAddEquiv with map_smul' := fun r x => e.map_mul r x }
  exact l.toModuleIso

/-- Equality of the actual coefficient points transports their original stalk modules. -/
def coefficientPointIso {D T Q : Scheme.{u}}
    (a : D ⟶ Q) (d : D) (b : T ⟶ Q) (t t' : T) (ht : t = t')
    (hp : a d = b t) (hp' : a d = b t') :
    (ModuleCat.restrictScalars (Intersection.coefficientStalkMap a d b t hp).hom).obj
        (ModuleCat.of (T.presheaf.stalk t) (T.presheaf.stalk t)) ≅
      Intersection.coefficientStalkModule a d b t' hp' := by
  subst t'
  exact Iso.refl _

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
  (C : IntegralClosedSubscheme (F.incidenceMap G).image)
  (P : FiniteCorrespondenceGenerator X.hom Z.hom)
  (hC : (C.val.subschemeι ≫ (F.incidenceMap G).imageι).ker = P.val)
  (w : P.incidence H)

local instance structureBaseNoetherian :
    IsLocallyNoetherian ((Functor.fromPUnit (Spec (.of k))).obj X.right) :=
  inferInstanceAs (IsLocallyNoetherian (Spec (.of k)))

local instance sourceLocallyNoetherian : IsLocallyNoetherian ((𝟭 Scheme).obj X.left) :=
  inferInstanceAs (IsLocallyNoetherian X.left)

local instance imageProductNoetherian : IsNoetherian (F.leftIntermediateImageProduct G H) :=
  ExteriorImageComponentEulerReplacement.imageProductNoetherian F G H

local instance intersectionAmbientNoetherian :
    IsLocallyNoetherian (correspondenceIntersectionAmbient X.hom Z.hom W.hom) :=
  isLocallyNoetherian_correspondenceIntersectionAmbient X.hom Z.hom W.hom

local instance incidenceNoetherian : IsLocallyNoetherian (P.incidence H) :=
  P.isLocallyNoetherian_incidence H

/-- The literal immersion ideal-sheaf quotient has the actual exterior stalk's
original image-product module action; the full nonreduced stalk is retained. -/
def remainingExteriorQuotientLinearEquiv :
    ModuleCat.of
        ((F.leftIntermediateImageProduct G H).presheaf.stalk
          (exteriorInclusion F G H C (remainingToExterior F G H C P hC w)))
        (((F.leftIntermediateImageProduct G H).presheaf.stalk
          (exteriorInclusion F G H C (remainingToExterior F G H C P hC w))) ⧸
            (exteriorInclusion F G H C).ker.stalk
              (exteriorInclusion F G H C (remainingToExterior F G H C P hC w))) ≃ₗ[
        (F.leftIntermediateImageProduct G H).presheaf.stalk
          (exteriorInclusion F G H C (remainingToExterior F G H C P hC w))]
      (ModuleCat.restrictScalars
        ((exteriorInclusion F G H C).stalkMap (remainingToExterior F G H C P hC w)).hom).obj
        (ModuleCat.of ((exterior F G H C).presheaf.stalk (remainingToExterior F G H C P hC w))
          ((exterior F G H C).presheaf.stalk (remainingToExterior F G H C P hC w))) :=
  closedStalkQuotientLinearEquiv (exteriorInclusion F G H C)
    (remainingToExterior F G H C P hC w)

/-- Both regularity and the literal kernel presentation concern the image of
the same given middle list in the actual four-factor ambient stalk. -/
theorem remainingExteriorAmbientList_regular_kernel
    (s : List ((pullback Z.hom Z.hom).presheaf.stalk
      (F.leftImageMiddlePair G H
        (exteriorInclusion F G H C (remainingToExterior F G H C P hC w)))))
    (hsreg : IsRegular ((pullback Z.hom Z.hom).presheaf.stalk
      (F.leftImageMiddlePair G H
        (exteriorInclusion F G H C (remainingToExterior F G H C P hC w)))) s)
    (hker : (pullback.diagonal Z.hom).ker.stalk
      (F.leftImageMiddlePair G H
        (exteriorInclusion F G H C (remainingToExterior F G H C P hC w))) = Ideal.ofList s) :
    IsRegular (P.incidenceAmbientStalk H w)
        (remainingExteriorAmbientList F G H C P hC w s) ∧
      RingHom.ker ((correspondenceTripleInclusion X.hom Z.hom W.hom).stalkMap
        (P.incidenceInclusion H w)).hom =
          Ideal.ofList (remainingExteriorAmbientList F G H C P hC w s) := by
  have hs := FiniteCorrespondenceGenerator.stalkCongr_regular
    (remainingExterior_middlePoint F G H C P hC w) s hsreg
  have hk := FiniteCorrespondenceGenerator.stalkCongr_kernel
    (pullback.diagonal Z.hom).ker (remainingExterior_middlePoint F G H C P hC w) s hker
  rw [(pullback.diagonal Z.hom).ker_stalk] at hk
  exact Diagonal.mapped_equations_regular_kernel
    (correspondenceTriple_isPullback X.hom Z.hom W.hom) (P.incidenceInclusion H w) hs hk

/-- The original coefficient module is obtained using the actual equality of
support-product points, rather than an unrelated identification of scalar rings. -/
def remainingExteriorCoefficientIso :
    (ModuleCat.restrictScalars
      (remainingExteriorCoefficientStalkMap F G H C P hC w).hom).obj
        (ModuleCat.of ((P.supportProduct H).presheaf.stalk
          ((exteriorIso F G H C P hC).hom (remainingToExterior F G H C P hC w)))
          ((P.supportProduct H).presheaf.stalk
            ((exteriorIso F G H C P hC).hom (remainingToExterior F G H C P hC w)))) ≅
      P.incidenceSupportStalkModule H w :=
  coefficientPointIso (correspondenceTripleInclusion X.hom Z.hom W.hom)
    (P.incidenceInclusion H w) (P.supportProductInclusion H) _ _
    (remainingExterior_supportPoint F G H C P hC w)
    (remainingExterior_ambientPoint F G H C P hC w)
    (Intersection.point_eq _ _ _ _ (P.incidence_ambient_isPullback H) w)

/-- The three actual surjective scalar maps preserve every Koszul homology
length. The same original remaining list is retained through their proved square. -/
theorem remainingExterior_restricted_length
    (s : List ((pullback Z.hom Z.hom).presheaf.stalk
      (F.leftImageMiddlePair G H
        (exteriorInclusion F G H C (remainingToExterior F G H C P hC w))))) (n : ℕ) :
    Module.length
      ((F.leftIntermediateImageProduct G H).presheaf.stalk
        (exteriorInclusion F G H C (remainingToExterior F G H C P hC w)))
      ((_root_.ChainComplex.Koszul.coefficientComplex
        ((ModuleCat.restrictScalars
          ((exteriorInclusion F G H C).stalkMap (remainingToExterior F G H C P hC w)).hom).obj
          (ModuleCat.of ((exterior F G H C).presheaf.stalk (remainingToExterior F G H C P hC w))
            ((exterior F G H C).presheaf.stalk (remainingToExterior F G H C P hC w))))
        (F.leftTargetRemainingList G H
          (exteriorInclusion F G H C (remainingToExterior F G H C P hC w)) s)).homology n) =
      Module.length (P.incidenceAmbientStalk H w)
        ((_root_.ChainComplex.Koszul.coefficientComplex (P.incidenceSupportStalkModule H w)
          (remainingExteriorAmbientList F G H C P hC w s)).homology n) := by
  let e := remainingToExterior F G H C P hC w
  let j := exteriorInclusion F G H C
  let D := (exterior F G H C).presheaf.stalk e
  let B := (P.supportProduct H).presheaf.stalk ((exteriorIso F G H C P hC).hom e)
  let l := (j.stalkMap e).hom
  let ε := (exteriorIso F G H C P hC).hom.stalkMap e
  let a := (remainingExteriorCoefficientStalkMap F G H C P hC w).hom
  let t := F.leftTargetRemainingList G H (j e) s
  let r := remainingExteriorAmbientList F G H C P hC w s
  let MD := ModuleCat.of D D
  let MB := ModuleCat.of B B
  let eB : MB ≅ (ModuleCat.restrictScalars ε.hom).obj MD :=
    regularModuleIso (asIso ε).commRingCatIsoToRingEquiv
  have ha : Function.Surjective a :=
    Intersection.coefficientStalkMap_surjective
      (correspondenceTripleInclusion X.hom Z.hom W.hom) (P.incidenceInclusion H w)
      (P.supportProductInclusion H) _ (remainingExterior_ambientPoint F G H C P hC w)
  calc
    _ = Module.length D ((_root_.ChainComplex.Koszul.coefficientComplex MD (t.map l)).homology n) :=
      _root_.ChainComplex.Koszul.coefficientRestrict_length l (j.stalkMap_surjective e) MD t n
    _ = Module.length D
        ((_root_.ChainComplex.Koszul.coefficientComplex MD ((r.map a).map ε.hom)).homology n) :=
      congrArg (fun q : List D => Module.length D ((_root_.ChainComplex.Koszul.coefficientComplex MD
          q).homology n))
        (remainingExterior_list_scalar_identity F G H C P hC w s)
    _ = Module.length B
        ((_root_.ChainComplex.Koszul.coefficientComplex ((ModuleCat.restrictScalars ε.hom).obj MD)
          (r.map a)).homology n) :=
      (_root_.ChainComplex.Koszul.coefficientRestrict_length ε.hom
        (asIso ε).commRingCatIsoToRingEquiv.surjective MD (r.map a) n).symm
    _ = Module.length B ((_root_.ChainComplex.Koszul.coefficientComplex MB (r.map a)).homology n) :=
      ((HomologicalComplex.homologyFunctor _ _ n).mapIso
        (_root_.ChainComplex.Koszul.coefficientIso eB (r.map a))).toLinearEquiv.length_eq.symm
    _ = Module.length (P.incidenceAmbientStalk H w)
        ((_root_.ChainComplex.Koszul.coefficientComplex ((ModuleCat.restrictScalars a).obj MB)
            r).homology n) :=
      (_root_.ChainComplex.Koszul.coefficientRestrict_length a ha MB r n).symm
    _ = _ :=
      ((HomologicalComplex.homologyFunctor _ _ n).mapIso
        (_root_.ChainComplex.Koszul.coefficientIso
          (remainingExteriorCoefficientIso F G H C P hC w) r)).toLinearEquiv.length_eq

omit w in
/-- The actual quotient-chain Euler equals the original generic-incidence Tor
coefficient. Both original regularity and literal diagonal generation are explicit. -/
theorem remainingQuotientEuler_eq_incidenceTorCoefficient
    (w : genericPoints (P.incidence H))
    (s : List ((pullback Z.hom Z.hom).presheaf.stalk
      (F.leftImageMiddlePair G H
        (exteriorInclusion F G H C (remainingToExterior F G H C P hC w.1)))))
    (hsreg : IsRegular ((pullback Z.hom Z.hom).presheaf.stalk
      (F.leftImageMiddlePair G H
        (exteriorInclusion F G H C (remainingToExterior F G H C P hC w.1)))) s)
    (hker : (pullback.diagonal Z.hom).ker.stalk
      (F.leftImageMiddlePair G H
        (exteriorInclusion F G H C (remainingToExterior F G H C P hC w.1))) = Ideal.ofList s) :
    let e := remainingToExterior F G H C P hC w.1
    let z := exteriorInclusion F G H C e
    let y := remainingToImage F G H C P hC w.1
    letI := F.leftTargetRemainingList_support_isArtinian G H z y
      (remainingToImage_mem_genericPoints k F G H C P hC w.1 w.2)
      (remainingExterior_imagePoint F G H C P hC w.1).symm s hker
    chainEuler (_root_.ChainComplex.Koszul.coefficientComplex
      (ModuleCat.of ((F.leftIntermediateImageProduct G H).presheaf.stalk z)
        (((F.leftIntermediateImageProduct G H).presheaf.stalk z) ⧸
          (exteriorInclusion F G H C).ker.stalk z))
      (F.leftTargetRemainingList G H z s))
      (_root_.ChainComplex.Koszul.finiteHomology_of_artinian_quotient_of_le_annihilator _ _ ⊥
          bot_le) =
      P.incidenceTorCoefficient H w := by
  let e := remainingToExterior F G H C P hC w.1
  let j := exteriorInclusion F G H C
  let z := j e
  let y := remainingToImage F G H C P hC w.1
  let := F.leftTargetRemainingList_support_isArtinian G H z y
    (remainingToImage_mem_genericPoints k F G H C P hC w.1 w.2)
    (remainingExterior_imagePoint F G H C P hC w.1).symm s hker
  let R := (F.leftIntermediateImageProduct G H).presheaf.stalk z
  let Q := ModuleCat.of R (R ⧸ j.ker.stalk z)
  let D := (exterior F G H C).presheaf.stalk e
  let N := (ModuleCat.restrictScalars (j.stalkMap e).hom).obj (ModuleCat.of D D)
  let t := F.leftTargetRemainingList G H z s
  let r := remainingExteriorAmbientList F G H C P hC w.1 s
  let K := _root_.ChainComplex.Koszul.coefficientComplex (P.incidenceSupportStalkModule H w.1) r
  obtain ⟨hr, hk⟩ := remainingExteriorAmbientList_regular_kernel F G H C P hC w.1 s hsreg hker
  have hK : FiniteHomology K :=
    (P.incidenceTor_finiteLengthSupport H w.1 w.2).of_iso (fun n =>
      Intersection.torIsoHomology (correspondenceTripleInclusion X.hom Z.hom W.hom)
        (P.incidenceInclusion H w.1) (P.supportProductInclusion H)
        (P.incidenceToSupportProduct H w.1)
        (Intersection.point_eq _ _ _ _ (P.incidence_ambient_isPullback H) w.1) r hk hr n)
  have hlen := remainingExterior_restricted_length F G H C P hC w.1 s
  have hN : FiniteHomology (_root_.ChainComplex.Koszul.coefficientComplex N t) :=
    finiteHomology_of_lengths hK hlen
  have hQ : FiniteHomology (_root_.ChainComplex.Koszul.coefficientComplex Q t) :=
    _root_.ChainComplex.Koszul.finiteHomology_of_artinian_quotient_of_le_annihilator Q t ⊥ bot_le
  have htor : P.incidenceTorCoefficient H w = chainEuler K hK :=
    Intersection.torEuler_eq_chainEuler (P.incidenceInclusion H)
      (P.incidenceToSupportProduct H) (correspondenceTripleInclusion X.hom Z.hom W.hom)
      (P.supportProductInclusion H) (P.incidence_ambient_isPullback H) w.1 w.2 r hk hr
  exact (_root_.ChainComplex.Koszul.coefficient_chainEuler_eq_of_linearEquiv Q N
    (remainingExteriorQuotientLinearEquiv F G H C P hC w.1) t hQ hN).trans
      ((chainEuler_eq_of_lengths hlen hN hK).trans htor.symm)

omit w in
/-- A fixed image point and its original list are retained. The necessary
point transport follows from the actual remaining-incidence square. -/
theorem remainingQuotientEuler_eq_incidenceTorCoefficient_fixedPoint
    (w : genericPoints (P.incidence H))
    (x : F.leftIntermediateImageProduct G H)
    (y : F.leftImageIncidence G H) (hy : y ∈ genericPoints (F.leftImageIncidence G H))
    (hp : x = F.leftImageIncidenceInclusion G H y)
    (hwy : remainingToImage F G H C P hC w.1 = y)
    (s : List ((pullback Z.hom Z.hom).presheaf.stalk (F.leftImageMiddlePair G H x)))
    (hsreg : IsRegular ((pullback Z.hom Z.hom).presheaf.stalk (F.leftImageMiddlePair G H x)) s)
    (hker : (pullback.diagonal Z.hom).ker.stalk (F.leftImageMiddlePair G H x) = Ideal.ofList s) :
    letI := F.leftTargetRemainingList_support_isArtinian G H x y hy hp s hker
    chainEuler (_root_.ChainComplex.Koszul.coefficientComplex
      (ModuleCat.of ((F.leftIntermediateImageProduct G H).presheaf.stalk x)
        (((F.leftIntermediateImageProduct G H).presheaf.stalk x) ⧸
          (exteriorInclusion F G H C).ker.stalk x))
      (F.leftTargetRemainingList G H x s))
      (_root_.ChainComplex.Koszul.finiteHomology_of_artinian_quotient_of_le_annihilator _ _ ⊥
          bot_le) =
      P.incidenceTorCoefficient H w := by
  have hx : x = exteriorInclusion F G H C (remainingToExterior F G H C P hC w.1) :=
    hp.trans ((congrArg (F.leftImageIncidenceInclusion G H) hwy).symm.trans
      (remainingExterior_imagePoint F G H C P hC w.1))
  subst hx
  exact remainingQuotientEuler_eq_incidenceTorCoefficient F G H C P hC w s hsreg hker

end Motivic.ExteriorImageRemainingTorAttachment
