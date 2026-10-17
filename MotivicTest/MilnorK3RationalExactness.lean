/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.KTheory.MilnorK3.RationalExactness
import Lean.Util.CollectAxioms

/-!
# Consumers and rejecting audit for actual rational-function K₃ exactness

These consumers retain the original groups and dependent finite residue target.
They use no norm, reciprocity, separability, or assumed exactness, and do not
assert injectivity of the constant map.
-/

open Polynomial
open Motivic.KTheory.MilnorK2 Motivic.KTheory.MilnorK3
open Motivic.KTheory.MilnorK3.PolynomialResidue
open Motivic.KTheory.MilnorK3.DegreeFiltration

noncomputable section

namespace MotivicTest.MilnorK3RationalExactness

variable {k : Type*} [Field k]

/-- Every actual finite dependent vector of original K₂ classes lifts. -/
theorem lift_actual_finite_residues
    (y : Π₀ p : MonicIrreducible k, K2 (AdjoinRoot p.val)) :
    ∃ x : K3 (RatFunc k), totalResidue x = y :=
  totalResidue_surjective y

/-- The lifted vector consists of the original polynomial residues, coordinatewise. -/
theorem lift_all_original_coordinates
    (y : Π₀ p : MonicIrreducible k, K2 (AdjoinRoot p.val)) :
    ∃ x : K3 (RatFunc k), ∀ p : MonicIrreducible k, residueAt p.val x = y p := by
  obtain ⟨x, hx⟩ := totalResidue_surjective y
  exact ⟨x, fun p => DFunLike.congr_fun hx p⟩

/-- A lift can preserve the support's polynomial degree bound. -/
theorem lift_with_actual_degree_bound (d : ℕ)
    (y : Π₀ p : MonicIrreducible k, K2 (AdjoinRoot p.val))
    (hy : ∀ p : MonicIrreducible k, d ≤ p.val.natDegree → y p = 0) :
    ∃ x ∈ lower k d, totalResidue x = y :=
  exists_mem_lower_totalResidue_eq d y hy

/-- The actual finite-place kernel equals the actual constant-map image. -/
theorem actual_kernel_equality :
    LinearMap.ker (totalResidue (k := k)) =
      LinearMap.range (Motivic.KTheory.MilnorK3.map (RatFunc.C : k →+* RatFunc k)) :=
  ker_totalResidue_eq_constant_range

/-- Every everywhere-unramified actual class is an image of a constant class. -/
theorem zero_residues_iff_constant_image (x : K3 (RatFunc k)) :
    (∀ p : MonicIrreducible k, residueAt p.val x = 0) ↔
      ∃ c : K3 k, Motivic.KTheory.MilnorK3.map (RatFunc.C : k →+* RatFunc k) c = x := by
  rw [← totalResidue_eq_zero_iff, totalResidue_eq_zero_iff_mem_constant_range]
  rfl

/-- Constant classes have zero actual finite residues. -/
theorem constants_have_zero_residues (c : K3 k) :
    totalResidue (Motivic.KTheory.MilnorK3.map (RatFunc.C : k →+* RatFunc k) c) = 0 :=
  totalResidue_map_constant c

/-- The quotient equivalence has literal original source and target modules. -/
def literal_quotient_equivalence :
    (K3 (RatFunc k) ⧸
      LinearMap.range (Motivic.KTheory.MilnorK3.map (RatFunc.C : k →+* RatFunc k))) ≃ₗ[ℤ]
      Π₀ p : MonicIrreducible k, K2 (AdjoinRoot p.val) :=
  quotientConstantEquivResidues

/-- Quotienting by constants preserves the actual residue formula. -/
theorem quotient_coordinate_is_actual_residue (x : K3 (RatFunc k))
    (p : MonicIrreducible k) :
    quotientConstantEquivResidues (Submodule.Quotient.mk x) p = residueAt p.val x := by
  rw [quotientConstantEquivResidues_mk, totalResidue_apply]

/-- High-degree vanishing applies to every actual class in the lower span. -/
theorem high_degree_residue_vanishes (d : ℕ) (x : K3 (RatFunc k))
    (hx : x ∈ lower k d) (p : MonicIrreducible k) (hp : d ≤ p.val.natDegree) :
    residueAt p.val x = 0 :=
  residueAt_eq_zero_of_mem_lower d x hx p hp

end MotivicTest.MilnorK3RationalExactness

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "The Milnor K₃ rational exactness audit requires legacy imports for private helpers"
  let libraryPrefixes := #[`Motivic.KTheory.MilnorK2, `Motivic.KTheory.MilnorK3,
    `Motivic.Aglib.RingTheory.PolynomialLocalResidue, `Polynomial.LocalResidue]
  let consumerPrefix := `MotivicTest.MilnorK3RationalExactness
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
        throwError "Milnor K₃ rational exactness declaration {name} is absent \
          from the kernel environment"
      count := count + 1
      for dependency in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Audited {count} Milnor K₂/K₃, polynomial local residue, and rational \
    exactness declarations, including private helpers: only standard Lean logical foundations."
