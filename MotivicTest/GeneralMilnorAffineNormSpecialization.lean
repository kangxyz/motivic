/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.KTheory.MilnorK.AffineNormSpecialization
import Lean.Util.CollectAxioms

/-! Direct consumers of actual arbitrary linear-place specialization, including
degree zero and original affine norm endpoint equality with no boundary premise. -/

namespace MotivicTest.GeneralMilnorAffineNormSpecialization

open Motivic.KTheory.MilnorK Polynomial
open PolynomialResidue DedekindResidue

section Constants

variable {k : Type*} [Field k]

local instance (a : k) : Fact (Irreducible (X - C a)) :=
  ⟨irreducible_X_sub_C a⟩

/-- Literal DVR specialization, followed by actual residue-field evaluation,
recovers an arbitrary original quotient class at every point. -/
theorem literal_linear_specialization (a : k) (n : ℕ) (x : K k n) :
    map n (linearRootEquiv a).toRingHom
      (specializeAt (X - C a) n (map n (RatFunc.C : k →+* RatFunc k) x)) = x :=
  linearSpecialization_constants a n x

/-- Recovery in degree zero includes every integer, not just the empty symbol. -/
theorem degree_zero_integer (a : k) (z : ℤ) :
    zeroEquiv k (linearSpecialization a 0
      (map 0 (RatFunc.C : k →+* RatFunc k) ((zeroEquiv k).symm z))) = z := by
  rw [linearSpecialization_constants, LinearEquiv.apply_symm_apply]

/-- The actual evaluated residue of a last-slot linear uniformizer recovers
an arbitrary constant quotient class in every degree. -/
theorem literal_linear_residue (a : k) (n : ℕ) (x : K k n) :
    map n (linearRootEquiv a).toRingHom
      (residueAt (X - C a) n
        (productUnit n (map n (RatFunc.C : k →+* RatFunc k) x)
          (Additive.ofMul (polynomialUnit (X - C a) (irreducible_X_sub_C a).ne_zero)))) = x :=
  linearResidue_productUnit_constants a n x

/-- Arbitrary constant-image classes have equal specializations at zero and one. -/
theorem zero_one_constant_image (n : ℕ) (x : K (RatFunc k) n)
    (hx : x ∈ LinearMap.range (map n (RatFunc.C : k →+* RatFunc k))) :
    linearSpecialization (0 : k) n x = linearSpecialization (1 : k) n x :=
  linearSpecialization_eq_of_mem_constant_range 0 1 n x hx

end Constants

section AffineNorm

universe u
variable (k S E : Type u) [Field k] [CharZero k]
  [CommRing S] [IsDedekindDomain S] [Algebra k[X] S] [Module.Finite k[X] S]
  [Module.IsTorsionFree k[X] S]
  [Field E] [Algebra S E] [IsFractionRing S E]
  [Algebra k[X] E] [IsScalarTower k[X] S E]
  [Algebra (RatFunc k) E] [IsScalarTower k[X] (RatFunc k) E]
  [FiniteDimensional (RatFunc k) E]

/-- The norm of any everywhere unramified class has equal endpoint values. -/
theorem all_class_norm_endpoints (a b : k) (n : ℕ) (x : K E (n + 1))
    (hx : totalResidue S E n x = 0) :
    linearSpecialization a (n + 1) (finiteExtensionNorm (RatFunc k) E (n + 1) x) =
      linearSpecialization b (n + 1) (finiteExtensionNorm (RatFunc k) E (n + 1) x) :=
  linearSpecialization_norm_eq_of_totalResidue_zero k S E a b n x hx

/-- Endpoint equality for the actual norm of original global-unit symbols
requires neither a supplied zero-residue premise nor a supplied boundary. -/
theorem actual_global_unit_norm_zero_one (n : ℕ) (u : Fin (n + 1) → Sˣ) :
    linearSpecialization (0 : k) (n + 1) (finiteExtensionNorm (RatFunc k) E (n + 1)
      (symbol (Units.map (algebraMap S E).toMonoidHom ∘ u))) =
      linearSpecialization (1 : k) (n + 1) (finiteExtensionNorm (RatFunc k) E (n + 1)
        (symbol (Units.map (algebraMap S E).toMonoidHom ∘ u))) :=
  linearSpecialization_norm_ring_unit_symbol_eq k S E 0 1 n u

/-- The two endpoint residues of the actual normalized norm, each with its own
literal last-slot linear uniformizer, agree without assuming a boundary. -/
theorem actual_norm_last_slot_endpoint_residues (a b : k) (n : ℕ)
    (u : Fin (n + 1) → Sˣ) :
    linearResidue a (n + 1)
      (productUnit (n + 1) (finiteExtensionNorm (RatFunc k) E (n + 1)
        (symbol (Units.map (algebraMap S E).toMonoidHom ∘ u)))
        (Additive.ofMul (polynomialUnit (X - C a) (irreducible_X_sub_C a).ne_zero))) =
      linearResidue b (n + 1)
        (productUnit (n + 1) (finiteExtensionNorm (RatFunc k) E (n + 1)
          (symbol (Units.map (algebraMap S E).toMonoidHom ∘ u)))
          (Additive.ofMul (polynomialUnit (X - C b) (irreducible_X_sub_C b).ne_zero))) := by
  rw [linearResidue_norm_ring_unit_symbol_productUnit k S E,
    linearResidue_norm_ring_unit_symbol_productUnit k S E]
  exact linearSpecialization_norm_ring_unit_symbol_eq k S E a b n u

end AffineNorm
end MotivicTest.GeneralMilnorAffineNormSpecialization

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`Motivic.KTheory.MilnorK,
    `MotivicTest.GeneralMilnorAffineNormSpecialization]
  let selected (name : Name) := prefixes.any (·.isPrefixOf name)
  let mut names : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    if selected env.header.moduleNames[i]! then
      for name in env.header.moduleData[i]!.constNames do
        names := names.insert name
  names := env.constants.foldStage2 (fun names name _ =>
    if selected name then names.insert name else names) names
  for name in names.toArray do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Checked {names.size} affine norm specialization and Milnor declarations: \
    standard axioms only."
