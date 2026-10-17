/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.GenericFinitePushforwardMultiplicity
public import Lean.Util.CollectAxioms

/-!
# Consumers of the original generic finite-pushforward multiplicity

The arbitrary-prime consumer retains the complete localized algebra and the
original map's residue degree. The scalar-square consumer checks the actual
map used in the degree comparison. No flatness or separability is assumed.
Every new public declaration is checked by a rejecting axiom audit.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic.MotivicTest.GenericFinitePushforwardMultiplicity

open FiniteFiber FiniteDomainGenericFiber Motivic.GenericFinitePushforwardMultiplicity

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (A B : CommRingCat.{u}) [IsDomain A] [IsDomain B]
  [Algebra A B] [Module.Finite A B]

/-- The whole generic length is finite before its integer conversion. -/
theorem whole_generic_length_finite (hAB : Function.Injective (algebraMap A B)) :
    Module.length (Localization.AtPrime (zeroPrime A).asIdeal)
        (localAlgebra A B (zeroPrime A)) ≠ ⊤ := by
  rw [wholeGeneric_length A B hAB]
  exact ENat.natCast_ne_top _

/-- Every target prime has the same actual original generic coefficient,
including target primes where the whole algebra has multiple branches. -/
theorem generic_degree_at_every_target_prime [IsNoetherianRing A]
    (p : PrimeSpectrum A) (hAB : Function.Injective (algebraMap A B)) :
    Koszul.domainGenericLength
        (Koszul.finiteFamilyRestriction (Localization.AtPrime p.asIdeal)
          (localAlgebra A B p) (ModuleCat.of (localAlgebra A B p) (localAlgebra A B p))) =
      ((Spec.map (CommRingCat.ofHom (algebraMap A B) : A ⟶ B)).residueDegree
        (zeroPrime B) : ℤ) :=
  localAlgebra_genericLength A B p hAB

/-- The identification retains the original pointed scheme residue map. -/
theorem original_generic_scalar_square (hAB : Function.Injective (algebraMap A B)) :
    CommRingCat.ofHom (algebraMap (Localization.AtPrime (zeroPrime A).asIdeal)
      (localAlgebra A B (zeroPrime A))) ≫ (wholeResidueIso A B hAB).hom =
      (Spec.stalkIso A (zeroPrime A)).inv ≫ (Spec A).residue (zeroPrime A) ≫
        pointedSpecResidueMap (CommRingCat.ofHom (algebraMap A B)) (zeroPrime A)
          (zeroPrime B) (zeroPrime_comap A B hAB) :=
  wholeResidueIso_base_square A B hAB

omit B [IsDomain B] [Algebra A B] [Module.Finite A B] in
/-- The actual identity coefficient is one at every target prime. -/
theorem identity_generic_length [IsNoetherianRing A] (p : PrimeSpectrum A) :
    Koszul.domainGenericLength
        (Koszul.finiteFamilyRestriction (Localization.AtPrime p.asIdeal)
          (localAlgebra A A p) (ModuleCat.of (localAlgebra A A p) (localAlgebra A A p))) =
      1 := by
  rw [localAlgebra_genericLength A A p (Function.injective_id),
    ← finrank_eq_residueDegree A A Function.injective_id, Module.finrank_self, Nat.cast_one]

open Lean in
run_cmd do
  for name in #[``wholeGeneric_length, ``finrank_eq_residueDegree,
      ``localAlgebra_genericLength, ``scheme_genericLength,
      ``whole_generic_length_finite, ``generic_degree_at_every_target_prime,
      ``original_generic_scalar_square, ``identity_generic_length] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Whole generic finite-pushforward multiplicities use only standard Lean foundations."

end Motivic.MotivicTest.GenericFinitePushforwardMultiplicity
