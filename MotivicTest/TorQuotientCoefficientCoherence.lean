/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.TorComparison.QuotientCoefficientCoherence
public import MotivicTest.TorQuotientFiniteness

/-! # Actual quotient-coefficient coherence for nonradical and higher-Tor inputs -/

@[expose] public section

noncomputable section

open CategoryTheory Motivic.TorComparison

namespace Motivic.MotivicTest.TorQuotientCoefficientCoherence

open TorQuotientFiniteness

/-- The first actual quotient coefficient map, with no flatness premise. -/
def firstQuotientMap : ℤ →+* Q := Ideal.Quotient.mk fourIdeal

/-- A second actual quotient ring map, still with no flatness premise. -/
def secondQuotientMap : Q →+* Q ⧸ Ideal.span ({(2 : Q)} : Set Q) :=
  Ideal.Quotient.mk _

/-- The actual nonradical quotient coefficient satisfies the canonical scalar unit law. -/
theorem fourQuotient_unit :
    (extendedIdealQuotientIso (RingHom.id ℤ) fourIdeal).hom ≫
      (mappedQuotientIdIso fourIdeal).hom =
    (ModuleCat.extendScalarsId ℤ).hom.app (ModuleCat.of ℤ Q) :=
  extendedIdealQuotientIso_hom_id fourIdeal

/-- Two actual quotient ring maps satisfy the canonical scalar associativity law. -/
theorem fourQuotient_comp :
    (ModuleCat.extendScalarsComp firstQuotientMap secondQuotientMap).hom.app
        (ModuleCat.of ℤ Q) ≫
      (ModuleCat.extendScalars secondQuotientMap).map
        (extendedIdealQuotientIso firstQuotientMap fourIdeal).hom ≫
      (extendedIdealQuotientIso secondQuotientMap (fourIdeal.map firstQuotientMap)).hom ≫
      (mappedQuotientCompIso firstQuotientMap secondQuotientMap fourIdeal).hom =
    (extendedIdealQuotientIso (secondQuotientMap.comp firstQuotientMap) fourIdeal).hom :=
  extendedIdealQuotientIso_hom_comp firstQuotientMap secondQuotientMap fourIdeal

/-- The same literal coefficient comparison acts on actual degree-one categorical Tor. -/
def higherTorCoefficientComparison :=
  extendedQuotientsTorIso (secondQuotientMap.comp firstQuotientMap) fourIdeal fourIdeal 1

/-- The coefficient ideal retained by these tests is genuinely nonradical. -/
theorem coefficientIdeal_not_radical : ¬ fourIdeal.IsRadical := fourIdeal_not_radical

/-- The degree-one Tor of the original coefficients is genuinely nonzero. -/
theorem originalHigherTor_nonzero :
    ¬ Limits.IsZero (((Tor (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ Q)).obj
      (ModuleCat.of ℤ Q)) := higherTor_nonzero

end Motivic.MotivicTest.TorQuotientCoefficientCoherence
