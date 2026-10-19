/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.QuotientScalarExtension
public import MotivicTest.TorQuotientFiniteness
public import Mathlib.RingTheory.Localization.BaseChange

/-! # Actual support-quotient restriction of nonzero higher Tor -/

@[expose] public section

noncomputable section

open CategoryTheory
open _root_.ComplexShape
open _root_.HomologicalComplex
open _root_.HomologicalComplex₂
open _root_.ModuleCat.TorComparison

namespace Motivic.MotivicTest.TorQuotientScalarExtension

open TorQuotientFiniteness

/-- The actual induced support ring map retains the specified ambient coordinate map. -/
theorem supportScalarSquare (R S : Type) [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) (r : R) :
    supportQuotientMap f I (Ideal.Quotient.mk I r) = Ideal.Quotient.mk (I.map f) (f r) :=
  supportQuotientMap_mk f I r

/-- A nonflat ambient quotient map can be used in this scalar-extension adapter. -/
def nonflatQuotientExample :=
  quotientScalarExtensionIso (Ideal.Quotient.mk (Ideal.span ({2} : Set ℤ)))
    fourIdeal (ModuleCat.of ℤ Q) (by simp only [Ideal.annihilator_quotient]; exact le_rfl)

/-- The construction accepts the actual nonzero degree-one Tor of Z/(4). -/
def higherTorRestriction :=
  quotientScalarExtensionIso (algebraMap ℤ (Localization (Submonoid.powers (3 : ℤ))))
    (fourIdeal ⊔ fourIdeal)
    (((Tor (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ Q)).obj (ModuleCat.of ℤ Q))
    (quotient_support_le_annihilator fourIdeal fourIdeal 1)

/-- Quotient scalar extension followed by canonical Tor base change gives a genuine
support-quotient-linear restriction map with no assumed coefficient flatness. -/
def canonicalSupportRestriction (R S : Type) [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Flat) (J K : Ideal R) (n : ℕ) :=
  quotientScalarExtensionIso f (J ⊔ K)
    (((Tor (ModuleCat R) n).obj (ModuleCat.of R (R ⧸ K))).obj (ModuleCat.of R (R ⧸ J)))
    (quotient_support_le_annihilator J K n) ≪≫
      flatBaseChangeTorQuotientIso f hf J K n

/-- The actual source module in the higher-Tor restriction is not a zero-module test. -/
theorem higherTorSource_nonzero :
    ¬ Limits.IsZero (((Tor (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ Q)).obj
      (ModuleCat.of ℤ Q)) := higherTor_nonzero

end Motivic.MotivicTest.TorQuotientScalarExtension
