/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Pushforward.Finite.Coefficients
public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.AmbientLength

/-!
# Euler lengths of actual finite affine pushforward stalk complexes

The original source and pushforward stalk complexes are compared to the whole
localized finite algebra and its genuine maximal-point localizations. Only
finite homology after extension to that whole algebra is assumed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom.FiniteFiber
open _root_.AlgebraicGeometry.Scheme.Modules _root_.PrimeSpectrum.FiniteFiber

open _root_.AlgebraicGeometry.Scheme.Modules.Pushforward.Affine
open _root_.HomologicalComplex.ModuleLengthEuler

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (A B : CommRingCat.{u}) [Algebra A B] [Module.Finite A B] (p : PrimeSpectrum A)

local instance sourceTilde_additive : (tilde.functor B).Additive :=
  AlgebraicGeometry.instAdditiveModuleCatCarrierModulesSpecFunctor

/-- The original B-complex extended to the whole localized finite algebra. -/
abbrev wholeCoefficientComplex (K : ChainComplex (ModuleCat.{u} B) ℕ) :=
  ((ModuleCat.extendScalars (algebraMap B (localAlgebra A B p))).mapHomologicalComplex _).obj K

/-- The actual structure-stalk-linear complex of the original affine pushforward. -/
abbrev actualPushforwardStalkComplex (K : ChainComplex (ModuleCat.{u} B) ℕ) :=
  (((tilde.functor B ⋙ Scheme.Modules.pushforward
    (Spec.map (CommRingCat.ofHom (algebraMap A B)))) ⋙
      Stalk.functor (X := Spec A) p).mapHomologicalComplex _).obj K

/-- The original source tilde complex at the actual source point. -/
abbrev actualSourceStalkComplex (x : PrimeSpectrum B) (K : ChainComplex (ModuleCat.{u} B) ℕ) :=
  ((tilde.functor B ⋙ Stalk.functor (X := Spec B) x).mapHomologicalComplex _).obj K

/-- The actual target stalk complex is the whole coefficient complex restricted to A_p,
through the canonical target structure-stalk isomorphism. -/
def primePushforwardComplexIso (K : ChainComplex (ModuleCat.{u} B) ℕ) :
    ((ModuleCat.restrictScalars (Spec.stalkIso A p).inv.hom).mapHomologicalComplex _).obj
        (actualPushforwardStalkComplex A B p K) ≅
      finiteAlgebraRestrictedComplex (Localization.AtPrime p.asIdeal) (localAlgebra A B p)
        (wholeCoefficientComplex A B p K) :=
  (NatIso.mapHomologicalComplex (pushforwardPrimeStalkIso A B p) _).app K

private theorem homologyLength_restrict_equiv {R T : Type u} [CommRing R] [CommRing T]
    (e : R ≃+* T) (K : ChainComplex (ModuleCat.{u} T) ℕ) (n : ℕ) :
    Module.length R
        ((((ModuleCat.restrictScalars e.toRingHom).mapHomologicalComplex _).obj K).homology n) =
      Module.length T (K.homology n) :=
  ((K.sc n).mapHomologyIso (ModuleCat.restrictScalars e.toRingHom)).toLinearEquiv.length_eq.trans
    (_root_.ModuleCat.length_restrictScalars_of_surjective e.toRingHom e.surjective _)

omit [Module.Finite A B] in
/-- The original pushforward stalk homology has precisely the A_p-length of
the restricted whole coefficient homology, in every degree. -/
theorem actualPushforwardStalk_homology_length (K : ChainComplex (ModuleCat.{u} B) ℕ) (n : ℕ) :
    Module.length ((Spec A).presheaf.stalk p) ((actualPushforwardStalkComplex A B p K).homology n) =
      Module.length (Localization.AtPrime p.asIdeal)
        ((finiteAlgebraRestrictedComplex (Localization.AtPrime p.asIdeal) (localAlgebra A B p)
          (wholeCoefficientComplex A B p K)).homology n) :=
  (homologyLength_restrict_equiv (Spec.stalkIso A p).symm.commRingCatIsoToRingEquiv
    (actualPushforwardStalkComplex A B p K) n).symm.trans
      ((HomologicalComplex.homologyFunctor _ _ n).mapIso
        (primePushforwardComplexIso A B p K)).toLinearEquiv.length_eq

/-- Localizing the whole coefficient gives the actual source homology length,
with no assertion that a single source stalk is finite over A_p. -/
theorem actualSourceStalk_homology_length (K : ChainComplex (ModuleCat.{u} B) ℕ)
    (q : MaximalSpectrum (localAlgebra A B p)) (n : ℕ) :
    Module.length (Localization.AtPrime q.asIdeal)
        ((finiteAlgebraLocalizedComplex (localAlgebra A B p)
          (wholeCoefficientComplex A B p K) q).homology n) =
      Module.length ((Spec B).presheaf.stalk (sourcePoint A B p q).1)
        ((actualSourceStalkComplex B (sourcePoint A B p q).1 K).homology n) :=
  ((HomologicalComplex.homologyFunctor _ _ n).mapIso
    ((localCoefficientStalkComplexIso A B p q _).app K)).toLinearEquiv.length_eq.trans
      (homologyLength_restrict_equiv (sourceSchemeStalkIso A B p q).commRingCatIsoToRingEquiv
        (actualSourceStalkComplex B (sourcePoint A B p q).1 K) n)

private theorem finiteHomology_of_length_eq {R T : Type u} [CommRing R] [CommRing T]
    {K : ChainComplex (ModuleCat.{u} R) ℕ} {L : ChainComplex (ModuleCat.{u} T) ℕ}
    (hK : FiniteHomology K)
    (h : ∀ n, Module.length R (K.homology n) = Module.length T (L.homology n)) :
    FiniteHomology L where
  finite_length n := by rw [← h n]; exact hK.finite_length n
  finite_support := by simpa only [show (fun n => Module.length R (K.homology n)) =
    (fun n => Module.length T (L.homology n)) from funext h] using hK.finite_support

private theorem homologyEuler_eq_of_length_eq {R T : Type u} [CommRing R] [CommRing T]
    {K : ChainComplex (ModuleCat.{u} R) ℕ} {L : ChainComplex (ModuleCat.{u} T) ℕ}
    (h : ∀ n, Module.length R (K.homology n) = Module.length T (L.homology n))
    (sign : ℕ → ℤ) (hK : FiniteHomology K) (hL : FiniteHomology L) :
    homologyEuler K sign hK = homologyEuler L sign hL := by
  unfold homologyEuler signedLengthSum
  apply finsum_congr
  intro n
  simp only [integerLength, h n]

variable [IsNoetherianRing (Localization.AtPrime p.asIdeal)]

/-- Genuine finite homology of the whole local coefficient complex implies
finite homology of the actual pushforward stalk, without any termwise length bound. -/
theorem actualPushforwardStalk_finiteHomology (K : ChainComplex (ModuleCat.{u} B) ℕ)
    (hK : FiniteHomology (wholeCoefficientComplex A B p K)) :
    FiniteHomology (actualPushforwardStalkComplex A B p K) :=
  finiteHomology_of_length_eq
    (hK.finiteAlgebra_restrict (Localization.AtPrime p.asIdeal) (localAlgebra A B p)
      (wholeCoefficientComplex A B p K))
    (fun n => (actualPushforwardStalk_homology_length A B p K n).symm)

/-- The same actual total finite homology implies finite homology at every
source stalk over the target point, derived through its true localized coefficient. -/
theorem actualSourceStalk_finiteHomology (K : ChainComplex (ModuleCat.{u} B) ℕ)
    (hK : FiniteHomology (wholeCoefficientComplex A B p K))
    (q : MaximalSpectrum (localAlgebra A B p)) :
    FiniteHomology (actualSourceStalkComplex B (sourcePoint A B p q).1 K) :=
  finiteHomology_of_length_eq
    (hK.finiteAlgebra_localized (Localization.AtPrime p.asIdeal) (localAlgebra A B p)
      (wholeCoefficientComplex A B p K) q)
    (actualSourceStalk_homology_length A B p K q)

/-- Every actual source point over p has finite stalk homology, with no
separate source finiteness premise. -/
theorem actualFiberStalk_finiteHomology (K : ChainComplex (ModuleCat.{u} B) ℕ)
    (hK : FiniteHomology (wholeCoefficientComplex A B p K))
    (x : {x : PrimeSpectrum B // x.comap (algebraMap A B) = p}) :
    FiniteHomology (actualSourceStalkComplex B x.1 K) := by
  have hx : (sourcePoint A B p ((maximalSpectrumEquivFiber A B p).symm x)).1 = x.1 :=
    congrArg Subtype.val ((maximalSpectrumEquivFiber A B p).apply_symm_apply x)
  have h := actualSourceStalk_finiteHomology A B p K hK
    ((maximalSpectrumEquivFiber A B p).symm x)
  exact (congrArg (fun z : PrimeSpectrum B =>
    FiniteHomology (actualSourceStalkComplex B z K)) hx).mp h

/-- The genuine finite affine pushforward Euler identity, over every actual
source point above p and with the literal scheme residue degree. Only the whole
local coefficient complex is required to have finite homology. -/
theorem actualFinitePushforwardEuler (K : ChainComplex (ModuleCat.{u} B) ℕ)
    (sign : ℕ → ℤ) (hK : FiniteHomology (wholeCoefficientComplex A B p K)) :
    homologyEuler (actualPushforwardStalkComplex A B p K) sign
        (actualPushforwardStalk_finiteHomology A B p K hK) =
      ∑ᶠ x : {x : PrimeSpectrum B // x.comap (algebraMap A B) = p},
        ((Spec.map (CommRingCat.ofHom (algebraMap A B))).residueDegree x.1 : ℤ) *
          homologyEuler (actualSourceStalkComplex B x.1 K) sign
            (actualFiberStalk_finiteHomology A B p K hK x) := by
  let L := wholeCoefficientComplex A B p K
  let R := Localization.AtPrime p.asIdeal
  let S := localAlgebra A B p
  have hR := hK.finiteAlgebra_restrict R S L
  have hq := fun q => hK.finiteAlgebra_localized R S L q
  calc
    _ = homologyEuler (finiteAlgebraRestrictedComplex R S L) sign hR :=
      homologyEuler_eq_of_length_eq (actualPushforwardStalk_homology_length A B p K) sign _ _
    _ = ∑ᶠ q : MaximalSpectrum S, (Module.finiteAlgebraResidueDegree R S q : ℤ) *
        homologyEuler (finiteAlgebraLocalizedComplex S L q) sign (hq q) := by
      let : Finite (MaximalSpectrum S) := Module.finiteAlgebra_maximalSpectrum_finite R S
      let : Fintype (MaximalSpectrum S) := Fintype.ofFinite _
      rw [finsum_eq_sum_of_fintype]
      exact homologyEuler_finiteAlgebra R S L sign hK
    _ = ∑ᶠ q : MaximalSpectrum S,
        ((Spec.map (CommRingCat.ofHom (algebraMap A B))).residueDegree
          (sourcePoint A B p q).1 : ℤ) *
        homologyEuler (actualSourceStalkComplex B (sourcePoint A B p q).1 K) sign
          (actualSourceStalk_finiteHomology A B p K hK q) := by
      apply finsum_congr
      intro q
      rw [finiteAlgebraResidueDegree_eq_schemeResidueDegree A B p q]
      congr 1
      exact homologyEuler_eq_of_length_eq (actualSourceStalk_homology_length A B p K q)
        sign _ _
    _ = _ := finsum_comp_equiv (maximalSpectrumEquivFiber A B p)
      (f := fun x => ((Spec.map (CommRingCat.ofHom (algebraMap A B))).residueDegree x.1 : ℤ) *
        homologyEuler (actualSourceStalkComplex B x.1 K) sign
          (actualFiberStalk_finiteHomology A B p K hK x))

/-- In particular, the alternating Euler characteristic has the actual finite
source-fiber pushforward formula. -/
theorem actualFinitePushforwardChainEuler (K : ChainComplex (ModuleCat.{u} B) ℕ)
    (hK : FiniteHomology (wholeCoefficientComplex A B p K)) :
    chainEuler (actualPushforwardStalkComplex A B p K)
        (actualPushforwardStalk_finiteHomology A B p K hK) =
      ∑ᶠ x : {x : PrimeSpectrum B // x.comap (algebraMap A B) = p},
        ((Spec.map (CommRingCat.ofHom (algebraMap A B))).residueDegree x.1 : ℤ) *
          chainEuler (actualSourceStalkComplex B x.1 K)
            (actualFiberStalk_finiteHomology A B p K hK x) :=
  actualFinitePushforwardEuler A B p K (fun n => (-1) ^ n) hK

end AlgebraicGeometry.Scheme.Hom.FiniteFiber
