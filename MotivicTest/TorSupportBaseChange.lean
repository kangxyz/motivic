/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.QuotientCoefficientExtension
public import MotivicTest.TorQuotientFiniteness
public import Mathlib.RingTheory.Localization.BaseChange

/-! # Actual literal-quotient support restriction, including nonzero higher Tor -/

@[expose] public section

noncomputable section

open CategoryTheory
open _root_.ComplexShape
open _root_.HomologicalComplex
open _root_.HomologicalComplex₂
open _root_.ModuleCat.TorComparison
open scoped TensorProduct ChangeOfRings

namespace Motivic.MotivicTest.TorSupportBaseChange

open TorQuotientFiniteness

/-- The actual ideal quotient extension is valid even for a nonflat ambient quotient map. -/
def nonflatCoefficientIso :=
  extendedIdealQuotientIso (Ideal.Quotient.mk (Ideal.span ({2} : Set ℤ))) fourIdeal

/-- Quotient representatives are carried by the actual tensor comparison. -/
theorem quotientRepresentative (s : ℤ ⧸ Ideal.span ({2} : Set ℤ)) (r : ℤ) :
    nonflatCoefficientIso.hom (s ⊗ₜ[ℤ,Ideal.Quotient.mk (Ideal.span ({2} : Set ℤ))]
      Ideal.Quotient.mk fourIdeal r) =
      Ideal.Quotient.mk (fourIdeal.map (Ideal.Quotient.mk (Ideal.span ({2} : Set ℤ))))
        (s * Ideal.Quotient.mk (Ideal.span ({2} : Set ℤ)) r) :=
  extendedIdealQuotientIso_hom_tmul _ _ _ _

/-- The support transition has literal image-ideal quotient coefficients for every localization. -/
def localizationSupportIso {R : Type} [CommRing R] (p : Submonoid R)
    (J K : Ideal R) (n : ℕ) :
    (ModuleCat.extendScalars (supportQuotientMapSup (algebraMap R (Localization p)) J K)).obj
      (torSupportModule J K n) ≅
      torSupportModule (J.map (algebraMap R (Localization p)))
        (K.map (algebraMap R (Localization p))) n :=
  torSupportBaseChangeIso _
    (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat (Localization p) p)) J K n

/-- A real nonradical, nonzero higher-Tor input is used by the literal support restriction. -/
def higherTorSupportRestriction :=
  localizationSupportIso (Submonoid.powers (3 : ℤ)) fourIdeal fourIdeal 1

/-- The source ideal in that actual restriction is nonradical. -/
theorem sourceIdeal_not_radical : ¬ fourIdeal.IsRadical := fourIdeal_not_radical

/-- The source Tor in that actual restriction is nonzero. -/
theorem sourceTor_nonzero :
    ¬ Limits.IsZero (((Tor (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ Q)).obj
      (ModuleCat.of ℤ Q)) := higherTor_nonzero

/-- Scalar extension commutes with doubling the actual higher-Tor coefficient. -/
theorem higherTorDouble_naturality :
    (ModuleCat.extendScalars (supportQuotientMap
      (algebraMap ℤ (Localization (Submonoid.powers (3 : ℤ)))) (fourIdeal ⊔ fourIdeal))).map
        (quotientLinearMap _ (quotient_support_le_annihilator fourIdeal fourIdeal 1)
          (quotient_support_le_annihilator fourIdeal fourIdeal 1) ((2 : ℤ) • 𝟙 _)) ≫
      (quotientScalarExtensionIso _ _ _
        (quotient_support_le_annihilator fourIdeal fourIdeal 1)).hom =
    (quotientScalarExtensionIso _ _ _
      (quotient_support_le_annihilator fourIdeal fourIdeal 1)).hom ≫
        quotientLinearMap _ _ _ ((ModuleCat.extendScalars
          (algebraMap ℤ (Localization (Submonoid.powers (3 : ℤ))))).map ((2 : ℤ) • 𝟙 _)) :=
  quotientScalarExtensionIso_hom_naturality _ _ _ _ _ _ _

end Motivic.MotivicTest.TorSupportBaseChange
