/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Scheme.StalkLocalization
public import Motivic.Aglib.AlgebraicGeometry.Stalk.KernelMinimalPrimes

/-!
# Global generic stalks from literal local minimal primes

The actual point equivalence from the stalk spectrum is upgraded to a scalar-
compatible localization of the global generic stalk. In particular, this does
not replace a generic component by a residue field or discard nilpotents.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- The literal local prime associated with a global component generic whose
closure contains the chosen point. -/
noncomputable def genericStalkLocalizationPrime (X : Scheme.{u}) (x : X)
    (y : {y : genericPoints X // y.1 ⤳ x}) : PrimeSpectrum (X.presheaf.stalk x) :=
  ((stalkGenericPointEquiv X x).symm y).1

/-- This prime is minimal in the original, possibly nonreduced stalk. -/
theorem genericStalkLocalizationPrime_mem_minimalPrimes (X : Scheme.{u}) (x : X)
    (y : {y : genericPoints X // y.1 ⤳ x}) :
    (genericStalkLocalizationPrime X x y).asIdeal ∈ minimalPrimes (X.presheaf.stalk x) :=
  (spec_mem_genericPoints_iff_minimalPrime _ _).mp ((stalkGenericPointEquiv X x).symm y).2

/-- The canonical stalk-spectrum map sends this actual prime to the given
global generic point, with no arbitrary choice of a geometric component. -/
theorem fromSpecStalk_genericStalkLocalizationPrime (X : Scheme.{u}) (x : X)
    (y : {y : genericPoints X // y.1 ⤳ x}) :
    X.fromSpecStalk x (genericStalkLocalizationPrime X x y) = y.1.1 :=
  congrArg (fun z : {y : genericPoints X // y.1 ⤳ x} => z.1.1)
    ((stalkGenericPointEquiv X x).apply_symm_apply y)

/-- The genuine global generic stalk is the original stalk localized at its
corresponding actual minimal prime. -/
noncomputable def genericStalkLocalizationIso (X : Scheme.{u}) (x : X)
    (y : {y : genericPoints X // y.1 ⤳ x}) :
    X.presheaf.stalk y.1.1 ≅
      CommRingCat.of (Localization.AtPrime (genericStalkLocalizationPrime X x y).asIdeal) :=
  X.presheaf.stalkCongr
      (Inseparable.of_eq (fromSpecStalk_genericStalkLocalizationPrime X x y).symm) ≪≫
    fromSpecStalkLocalizationIso X x (genericStalkLocalizationPrime X x y)

set_option backward.isDefEq.respectTransparency.types false in
/-- The localization identification respects the actual global specialization
map from the original stalk, rather than an artificially transported action. -/
@[reassoc]
theorem stalkSpecializes_genericStalkLocalizationIso (X : Scheme.{u}) (x : X)
    (y : {y : genericPoints X // y.1 ⤳ x}) :
    X.presheaf.stalkSpecializes y.2 ≫ (genericStalkLocalizationIso X x y).hom =
      CommRingCat.ofHom (algebraMap (X.presheaf.stalk x)
        (Localization.AtPrime (genericStalkLocalizationPrime X x y).asIdeal)) := by
  rw [genericStalkLocalizationIso, Iso.trans_hom, ← Category.assoc,
    TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_comp]
  exact stalkSpecializes_fromSpecStalkLocalizationIso X x (genericStalkLocalizationPrime X x y)

/-- The scalar-compatible algebra equivalence at an actual global generic. -/
noncomputable def genericStalkLocalizationAlgEquiv (X : Scheme.{u}) (x : X)
    (y : {y : genericPoints X // y.1 ⤳ x}) :
    letI : Algebra (X.presheaf.stalk x) (X.presheaf.stalk y.1.1) :=
      (X.presheaf.stalkSpecializes y.2).hom.toAlgebra
    X.presheaf.stalk y.1.1 ≃ₐ[X.presheaf.stalk x]
      Localization.AtPrime (genericStalkLocalizationPrime X x y).asIdeal := by
  letI : Algebra (X.presheaf.stalk x) (X.presheaf.stalk y.1.1) :=
    (X.presheaf.stalkSpecializes y.2).hom.toAlgebra
  exact { (genericStalkLocalizationIso X x y).commRingCatIsoToRingEquiv with
    commutes' := fun r => ConcreteCategory.congr_hom
      (stalkSpecializes_genericStalkLocalizationIso X x y) r }

/-- The actual generic stalk, with its actual specialization action, is a
localization at the corresponding minimal prime. -/
theorem isLocalization_genericStalk (X : Scheme.{u}) (x : X)
    (y : {y : genericPoints X // y.1 ⤳ x}) :
    letI : Algebra (X.presheaf.stalk x) (X.presheaf.stalk y.1.1) :=
      (X.presheaf.stalkSpecializes y.2).hom.toAlgebra
    IsLocalization.AtPrime (X.presheaf.stalk y.1.1)
      (genericStalkLocalizationPrime X x y).asIdeal := by
  let : Algebra (X.presheaf.stalk x) (X.presheaf.stalk y.1.1) :=
    (X.presheaf.stalkSpecializes y.2).hom.toAlgebra
  exact IsLocalization.isLocalization_of_algEquiv
    (genericStalkLocalizationPrime X x y).asIdeal.primeCompl
    (genericStalkLocalizationAlgEquiv X x y).symm

/-- For a genuine surjective ambient stalk map, the prime used in the global
stalk localization contracts to the originally supplied kernel-minimal prime. -/
theorem genericStalkLocalizationPrime_kernel_comap {Z T : Scheme.{u}} (i : Z ⟶ T)
    [SurjectiveOnStalks i] (z : Z)
    (p : (RingHom.ker (i.stalkMap z).hom).minimalPrimes) :
    (genericStalkLocalizationPrime Z z (stalkKernelGenericEquiv i z p)).asIdeal.comap
        (i.stalkMap z).hom = p.1 := by
  have h := stalkKernelGenericEquiv_symm_val i z (stalkKernelGenericEquiv i z p)
  simpa only [genericStalkLocalizationPrime, Equiv.symm_apply_apply] using h.symm

end AlgebraicGeometry.Scheme
