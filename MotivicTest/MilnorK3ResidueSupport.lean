/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.KTheory.MilnorK3.ResidueSupport
import Lean.Util.CollectAxioms

/-!
# Actual finite-residue support consumers and rejecting axiom audit

These consumers use arbitrary classes of the actual nested Milnor quotient,
actual rational-function numerators and denominators, and the dependent sum
of the original residue-field K₂ groups. No support, norm, separability, or
exactness premise is added. Legacy imports expose private implementation
helpers for the complete rejecting standard-foundations audit.
-/

open Polynomial
open Motivic.KTheory.MilnorK2 Motivic.KTheory.MilnorK3
open Motivic.KTheory.MilnorK3.PolynomialResidue

noncomputable section

namespace MotivicTest.MilnorK3ResidueSupport

variable {k : Type*} [Field k]

/-- Numerator and denominator expansion is an equality of literal field units. -/
theorem literal_rational_unit_expansion (a : (RatFunc k)ˣ) :
    Units.mk0 (algebraMap k[X] (RatFunc k) (a : RatFunc k).num)
        (RatFunc.algebraMap_ne_zero (RatFunc.num_ne_zero a.ne_zero)) /
      Units.mk0 (algebraMap k[X] (RatFunc k) (a : RatFunc k).denom)
        (RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero _)) = a :=
  polynomialUnit_num_div_denom a

/-- The six actual numerator and denominator factors bound every symbol residue. -/
theorem literal_symbol_support_bound (a b c : (RatFunc k)ˣ) :
    {p : MonicIrreducible k | residueAt p.val (symbol3 a b c) ≠ 0} ⊆
      {p | p.val ∣ (a : RatFunc k).num * (a : RatFunc k).denom *
        (b : RatFunc k).num * (b : RatFunc k).denom *
        (c : RatFunc k).num * (c : RatFunc k).denom} :=
  residueAt_symbol_support_subset a b c

/-- Finiteness applies to an arbitrary actual quotient class, not only symbols. -/
theorem arbitrary_class_finite_support (x : K3 (RatFunc k)) :
    Set.Finite {p : MonicIrreducible k | residueAt p.val x ≠ 0} :=
  finite_residueAt_support x

/-- A finite set simultaneously controls every actual polynomial residue of a class. -/
theorem arbitrary_class_finite_bound (x : K3 (RatFunc k)) :
    ∃ s : Finset (MonicIrreducible k), ∀ p, p ∉ s → residueAt p.val x = 0 := by
  classical
  refine ⟨(finite_residueAt_support x).toFinset, ?_⟩
  intro p hp
  simpa using hp

/-- The total residue takes values in the original dependent family of K₂ groups. -/
theorem actual_dependent_target (x : K3 (RatFunc k)) :
    ∃ y : Π₀ p : MonicIrreducible k,
      TensorProduct ℤ (Additive (AdjoinRoot p.val)ˣ) (Additive (AdjoinRoot p.val)ˣ) ⧸
        steinbergSpan (AdjoinRoot p.val),
      ∀ p, y p = residueAt p.val x :=
  ⟨totalResidue x, totalResidue_apply x⟩

/-- Every coordinate is the actual local DVR residue followed by the original K₂ field map. -/
theorem total_actual_composition (x : K3 (RatFunc k)) (p : MonicIrreducible k) :
    totalResidue x p =
      Motivic.KTheory.MilnorK2.map (LocalResidue.residueEquiv p.val).toRingHom
        (Motivic.KTheory.MilnorK3.DVR.residue
          (Localization.AtPrime (Ideal.span {p.val})) (RatFunc k) x) := rfl

/-- The actual total residue preserves addition and subtraction of arbitrary classes. -/
theorem total_residue_sub (x y : K3 (RatFunc k)) :
    totalResidue (x - y) = totalResidue x - totalResidue y :=
  map_sub totalResidue x y

/-- The actual total residue is integer-linear on arbitrary classes. -/
theorem total_residue_smul (n : ℤ) (x : K3 (RatFunc k)) :
    totalResidue (n • x) = n • totalResidue x :=
  map_smul totalResidue n x

open scoped Classical in
/-- The finite support of the constructed dependent function is exactly the actual support. -/
theorem total_support_exact (x : K3 (RatFunc k)) :
    ↑(totalResidue x).support =
      {p : MonicIrreducible k | residueAt p.val x ≠ 0} := by
  ext p
  simp

/-- Vanishing of the total residue tests precisely all actual finite-polynomial residues. -/
theorem total_zero_iff_all_actual_residues_zero (x : K3 (RatFunc k)) :
    totalResidue x = 0 ↔ ∀ p : MonicIrreducible k, residueAt p.val x = 0 :=
  totalResidue_eq_zero_iff x

/-- First-slot polynomial normalization survives packaging into the dependent finite sum. -/
theorem total_normalization (p : MonicIrreducible k) (q r : k[X])
    (hq : q ≠ 0) (hr : r ≠ 0)
    (hqdeg : q.natDegree < p.val.natDegree) (hrdeg : r.natDegree < p.val.natDegree) :
    totalResidue (symbol3 (polynomialUnit p.val p.property.2.ne_zero)
      (polynomialUnit q hq) (polynomialUnit r hr)) p =
      symbol (quotientUnit p.val q (p.property.1.not_dvd_of_natDegree_lt hq hqdeg))
        (quotientUnit p.val r (p.property.1.not_dvd_of_natDegree_lt hr hrdeg)) :=
  residueAt_reduced p.val p.property.1 q r hq hr hqdeg hrdeg

end MotivicTest.MilnorK3ResidueSupport

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "The Milnor residue support audit requires legacy imports for private helpers"
  let libraryPrefixes := #[`Motivic.KTheory.MilnorK2, `Motivic.KTheory.MilnorK3,
    `Motivic.Aglib.RingTheory.PolynomialLocalResidue, `Polynomial.LocalResidue]
  let consumerPrefix := `MotivicTest.MilnorK3ResidueSupport
  let isLibrary (name : Name) : Bool := libraryPrefixes.any (·.isPrefixOf name)
  let selected (name : Name) : Bool :=
    let libraryOrigin := match env.getModuleIdxFor? name with
      | some index => isLibrary env.header.moduleNames[index.toNat]!
      | none => false
    libraryOrigin || isLibrary name || consumerPrefix.isPrefixOf name
  let mut names : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    let libraryOrigin := isLibrary env.header.moduleNames[i]!
    for name in env.header.moduleData[i]!.constNames do
      if libraryOrigin || isLibrary name then
        names := names.insert name
  names := env.constants.foldStage2 (fun names name _ =>
    if selected name then names.insert name else names) names
  let mut count : Nat := 0
  for name in names.toArray do
    if selected name then
      unless (env.checked.get.find? name).isSome do
        throwError "Milnor residue support declaration {name} is absent from \
          the kernel environment"
      count := count + 1
      for dependency in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Audited {count} Milnor K₂/K₃, polynomial local residue, and consumer declarations, \
    including private helpers: only standard Lean logical foundations."
