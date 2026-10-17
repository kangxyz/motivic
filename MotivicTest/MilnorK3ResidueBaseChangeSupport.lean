/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.KTheory.MilnorK3.ResidueBaseChangeSupport
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Lean.Util.CollectAxioms

/-!
# Actual coefficient-extension support consumers and rejecting axiom audit

These consumers retain the original Milnor quotient groups, actual polynomial
and rational-function maps, and concrete finite sets of target factors. A
transcendental coefficient extension supplies a target finite place with zero
contraction, so the missing-contraction branch is tested on an actual example.
-/

open Polynomial Polynomial.LocalResidue
open Motivic.KTheory.MilnorK3
open Motivic.KTheory.MilnorK3.PolynomialResidue

noncomputable section

namespace MotivicTest.MilnorK3ResidueBaseChangeSupport

variable {k L : Type*} [Field k] [Field L]

/-- The source factor genuinely divides the original nonzero polynomial. -/
theorem actual_source_factor (φ : k →+* L) (q : L[X]) (hq : Irreducible q)
    (a : k[X]) (ha : a ≠ 0) (hqa : q ∣ a.map φ) :
    ∃ p : k[X], p.Monic ∧ Irreducible p ∧ p ∣ a ∧ q ∣ p.map φ :=
  exists_monic_irreducible_dvd_of_dvd_map φ q hq a ha hqa

/-- A target place cannot lie above two distinct normalized source places. -/
theorem actual_source_unique (φ : k →+* L) (p r : MonicIrreducible k)
    (q : MonicIrreducible L) (hqp : q.val ∣ p.val.map φ) (hqr : q.val ∣ r.val.map φ) :
    p = r := by
  apply Subtype.ext
  exact monic_irreducible_eq_of_dvd_map φ p.val r.val q.val
    p.property.1 r.property.1 hqp hqr

/-- The actual scalar extension of every rational-function polynomial unit. -/
theorem actual_mapped_polynomial_unit (φ : k →+* L) (a : k[X]) (ha : a ≠ 0) :
    Units.map (fractionMap φ).toMonoidHom
        (Units.mk0 (algebraMap k[X] (RatFunc k) a) (RatFunc.algebraMap_ne_zero ha)) =
      Units.mk0 (algebraMap L[X] (RatFunc L) (a.map φ))
        (RatFunc.algebraMap_ne_zero (Polynomial.map_ne_zero ha)) :=
  unitsMap_polynomialUnit φ a ha

/-- Over the transcendental coefficient extension, `X - C(t)` divides no
coefficient image of a nonzero source polynomial. -/
theorem transcendental_place_has_zero_contraction (a : k[X]) (ha : a ≠ 0) :
    ¬(X - C (RatFunc.X : RatFunc k)) ∣ a.map (RatFunc.C : k →+* RatFunc k) := by
  intro h
  have heval := Polynomial.dvd_iff_isRoot.mp h
  change (a.map (RatFunc.C : k →+* RatFunc k)).eval RatFunc.X = 0 at heval
  rw [Polynomial.eval_map] at heval
  have heval' : a.aeval (RatFunc.X : RatFunc k) = 0 := heval
  rw [RatFunc.aeval_X_left_eq_algebraMap] at heval'
  exact RatFunc.algebraMap_ne_zero ha heval'

local instance : Fact (Irreducible (X - C (RatFunc.X : RatFunc k))) :=
  ⟨Polynomial.irreducible_X_sub_C _⟩

/-- The zero-contraction target place kills every restricted original K₃ class,
even without a characteristic-zero assumption. -/
theorem actual_transcendental_place_vanishing (x : K3 (RatFunc k)) :
    residueAt (X - C (RatFunc.X : RatFunc k)) (Motivic.KTheory.MilnorK3.map
      (fractionMap (RatFunc.C : k →+* RatFunc k)) x) = 0 := by
  exact residueAt_restrict_zero_of_no_polynomial_divisor
    (RatFunc.C : k →+* RatFunc k) _ transcendental_place_has_zero_contraction x

variable [CharZero k]

/-- Every actual factor coordinate is the literal quotient-field K₂ map. -/
theorem original_factor_coordinate (φ : k →+* L) (p : MonicIrreducible k)
    (z : Motivic.KTheory.MilnorK2.K2 (AdjoinRoot p.val)) (x : K3 (RatFunc k))
    [DecidableEq (MonicIrreducible k)] (hx : totalResidue x = DFinsupp.single p z)
    (q : MonicIrreducible L) (hq : q.val ∣ p.val.map φ) :
    totalResidue (Motivic.KTheory.MilnorK3.map (fractionMap φ) x) q =
      Motivic.KTheory.MilnorK2.map (adjoinRootMap φ p.val q.val hq) z :=
  totalResidue_restrict_single_of_dvd φ p z x hx q hq

/-- Off-factor vanishing applies to arbitrary target places, not only those
already equipped with a source contraction. -/
theorem original_off_factor_coordinate (φ : k →+* L) (p : MonicIrreducible k)
    (z : Motivic.KTheory.MilnorK2.K2 (AdjoinRoot p.val)) (x : K3 (RatFunc k))
    [DecidableEq (MonicIrreducible k)] (hx : totalResidue x = DFinsupp.single p z)
    (q : MonicIrreducible L) (hq : ¬q.val ∣ p.val.map φ) :
    totalResidue (Motivic.KTheory.MilnorK3.map (fractionMap φ) x) q = 0 :=
  totalResidue_restrict_single_of_not_dvd φ p z x hx q hq

open scoped Classical in
/-- A finite set of literal polynomial factors bounds the actual dependent support. -/
theorem original_finite_support (φ : k →+* L) (p : MonicIrreducible k)
    (z : Motivic.KTheory.MilnorK2.K2 (AdjoinRoot p.val)) (x : K3 (RatFunc k))
    (hx : totalResidue x = DFinsupp.single p z) :
    (totalResidue (Motivic.KTheory.MilnorK3.map (fractionMap φ) x)).support ⊆
      placesAbove φ p :=
  totalResidue_restrict_single_support_subset φ p z x hx

omit [CharZero k] in
/-- Finite-factor membership is exactly divisibility, with no assumed splitting. -/
theorem original_factor_set (φ : k →+* L) (p : MonicIrreducible k)
    (q : MonicIrreducible L) : q ∈ placesAbove φ p ↔ q.val ∣ p.val.map φ :=
  mem_placesAbove φ p q

end MotivicTest.MilnorK3ResidueBaseChangeSupport

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "The residue base-change support audit requires legacy imports for private helpers"
  let libraryPrefixes := #[`Motivic.KTheory.MilnorK2, `Motivic.KTheory.MilnorK3,
    `Motivic.Aglib.RingTheory.PolynomialLocalResidue,
    `Motivic.Aglib.RingTheory.PolynomialResidueBaseChange,
    `Motivic.Aglib.RingTheory.PolynomialPlaceContraction,
    `Motivic.Aglib.FieldTheory.RatFuncCoefficientMap, `Polynomial.LocalResidue]
  let consumerPrefix := `MotivicTest.MilnorK3ResidueBaseChangeSupport
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
        throwError "Milnor residue base-change support declaration {name} is absent from \
          the kernel environment"
      count := count + 1
      for dependency in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Audited {count} actual Milnor K₂/K₃, polynomial-place base-change, and consumer \
    declarations, including private helpers: only standard Lean logical foundations."
