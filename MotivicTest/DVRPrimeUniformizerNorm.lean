/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.Aglib.RingTheory.DVRPrimeUniformizerNorm
import Lean.Util.CollectAxioms

/-! Direct consumers of the combined exact prime-degree coefficient. The
exponent-one consumer has no henselianity or primality assumption. -/

open IsLocalRing

namespace MotivicTest.DVRPrimeUniformizerNorm

variable (R S F E : Type*)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [IsLocalHom (algebraMap R S)]
  [Field F] [Algebra R F] [IsFractionRing R F] [PerfectField F]
  [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
  [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
  [IsIntegralClosure S R E] [FiniteDimensional F E]
  {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)

include F E hπ hϖ

/-- Exponent one does not require Hensel lifting or a prime-degree extension. -/
theorem exponent_one (u : Sˣ) (he : algebraMap R S π = (u : S) * ϖ) :
    ∃ b : Rˣ, Algebra.intNorm R S ϖ =
        π ^ Module.finrank (ResidueField R) (ResidueField S) * (b : R) ∧
      residue R (b : R) =
        (Algebra.norm (ResidueField R) (residue S (u : S)))⁻¹ :=
  IsDiscreteValuationRing.exists_uniformizer_norm_coefficient_of_exponent_one
    R S F E hπ hϖ u he

variable [HenselianLocalRing S]
  (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
  (hp : Nat.Prime (Module.finrank F E))

include he hp

/-- Both actual prime-degree branches have one common coefficient formula. -/
theorem prime_coefficient (heunit : IsUnit (e : S)) :
    ∃ b : Rˣ, Algebra.intNorm R S ϖ =
        π ^ Module.finrank (ResidueField R) (ResidueField S) * (b : R) ∧
      residue R (b : R) =
        (-1 : ResidueField R) ^ (Module.finrank (ResidueField R) (ResidueField S) * (e - 1)) *
          (Algebra.norm (ResidueField R) (residue S (u : S)))⁻¹ :=
  IsDiscreteValuationRing.exists_uniformizer_norm_coefficient_of_prime_degree
    R S F E hπ hϖ u e he heunit hp

/-- The exact integral identity transports to the original ordinary field norm. -/
theorem ordinary_field_norm_coefficient (heunit : IsUnit (e : S)) :
    ∃ b : Rˣ, Algebra.norm F (algebraMap S E ϖ) =
        algebraMap R F π ^ Module.finrank (ResidueField R) (ResidueField S) *
          algebraMap R F (b : R) ∧
      residue R (b : R) =
        (-1 : ResidueField R) ^ (Module.finrank (ResidueField R) (ResidueField S) * (e - 1)) *
          (Algebra.norm (ResidueField R) (residue S (u : S)))⁻¹ := by
  obtain ⟨b, hb, hbres⟩ := prime_coefficient R S F E hπ hϖ u e he hp heunit
  refine ⟨b, ?_, hbres⟩
  rw [← Algebra.algebraMap_intNorm (A := R) (K := F) (L := E), hb, map_mul, map_pow]

/-- Residue characteristic zero gives the invertible exponent from actual e>0. -/
theorem residue_characteristic_zero [CharZero (ResidueField S)] :
    ∃ b : Rˣ, Algebra.intNorm R S ϖ =
        π ^ Module.finrank (ResidueField R) (ResidueField S) * (b : R) ∧
      residue R (b : R) =
        (-1 : ResidueField R) ^ (Module.finrank (ResidueField R) (ResidueField S) * (e - 1)) *
          (Algebra.norm (ResidueField R) (residue S (u : S)))⁻¹ := by
  have hd := IsDiscreteValuationRing.finrank_eq_ramification_mul_residue_finrank
    R S F E hπ hϖ u e he
  have hepos : 0 < e := by
    apply Nat.pos_of_ne_zero
    intro hz
    rw [hz, zero_mul] at hd
    exact hp.ne_zero hd
  exact prime_coefficient R S F E hπ hϖ u e he hp
    (Motivic.HenselianPrincipalRoots.isUnit_natCast_of_residue_charZero e hepos)

end MotivicTest.DVRPrimeUniformizerNorm

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let native := #[`IsDiscreteValuationRing.exists_uniformizer_norm_coefficient_of_exponent_one,
    `IsDiscreteValuationRing.exists_uniformizer_norm_coefficient_of_prime_degree]
  let selected (name : Name) := native.contains name ||
    (`MotivicTest.DVRPrimeUniformizerNorm).isPrefixOf name
  let mut names : NameSet := {}
  for name in native do names := names.insert name
  names := env.constants.foldStage2 (fun names name _ =>
    if selected name then names.insert name else names) names
  for name in names.toArray do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Checked {names.size} exact prime uniformizer-norm declarations: standard axioms only."
