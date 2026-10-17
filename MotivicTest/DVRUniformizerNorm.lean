/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.Aglib.RingTheory.DVRUniformizerNorm
import Motivic.Aglib.RingTheory.CompleteDVRExtension
import Lean.Util.CollectAxioms

/-! Direct coefficient consumers retain the actual ring norm, genuine
residue degree one, exponent invertibility and the exact determinant sign.
The complete-DVR consumer constructs the henselian integral closure. -/

open IsLocalRing

namespace MotivicTest.DVRUniformizerNorm

section ActualExtension

variable (R S F E : Type*)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [HenselianLocalRing S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [IsLocalHom (algebraMap R S)]
  [Field F] [Algebra R F] [IsFractionRing R F] [PerfectField F]
  [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
  [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
  [IsIntegralClosure S R E] [FiniteDimensional F E]
  {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
  (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
  (hf : Module.finrank (ResidueField R) (ResidueField S) = 1)

include F E hπ hϖ he hf

/-- An actual unit is returned as the normalized coefficient. -/
theorem exact_coefficient (heunit : IsUnit (e : S)) :
    ∃ b : Rˣ, Algebra.intNorm R S ϖ = π * (b : R) ∧
      residue R (b : R) = (-1 : ResidueField R) ^ (e - 1) *
        (Algebra.norm (ResidueField R) (residue S (u : S)))⁻¹ :=
  IsDiscreteValuationRing.exists_uniformizer_norm_coefficient_of_residue_finrank_one
    R S F E hπ hϖ u e he heunit hf

omit he in
/-- The quadratic case keeps the negative sign. -/
theorem quadratic_sign (he2 : algebraMap R S π = (u : S) * ϖ ^ 2)
    (h2 : IsUnit (2 : S)) :
    ∃ b : Rˣ, Algebra.intNorm R S ϖ = π * (b : R) ∧
      residue R (b : R) = -(Algebra.norm (ResidueField R) (residue S (u : S)))⁻¹ := by
  simpa using exact_coefficient R S F E hπ hϖ u 2 he2 hf h2

/-- Residue characteristic zero explicitly supplies invertibility. -/
theorem residue_characteristic_zero [CharZero (ResidueField S)] :
    ∃ b : Rˣ, Algebra.intNorm R S ϖ = π * (b : R) ∧
      residue R (b : R) = (-1 : ResidueField R) ^ (e - 1) *
        (Algebra.norm (ResidueField R) (residue S (u : S)))⁻¹ := by
  have hd := IsDiscreteValuationRing.finrank_eq_ramification_mul_residue_finrank
    R S F E hπ hϖ u e he
  have hp : 0 < e := by
    have hpos := Module.finrank_pos (R := F) (M := E)
    rw [hd, hf, mul_one] at hpos
    exact hpos
  exact exact_coefficient R S F E hπ hϖ u e he hf
    (Motivic.HenselianPrincipalRoots.isUnit_natCast_of_residue_charZero e hp)

end ActualExtension

section Complete

variable (R F E : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R] [CharZero (ResidueField R)]
  [Field F] [Algebra R F] [IsFractionRing R F] [PerfectField F]
  [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
  [FiniteDimensional F E]

/-- Completeness supplies the actual henselian DVR integral closure. Residue
characteristic zero is transported through its genuine residue algebra map. -/
theorem complete_DVR_coefficient :
    let _ := Motivic.CompleteDVRExtension.integralClosure_isDiscreteValuationRing R F E
    let _ := Motivic.CompleteDVRExtension.integralClosure_henselianLocalRing R F E
    let _ := Motivic.CompleteDVRExtension.integralClosure_isLocalHom R F E
    let _ : Module.IsTorsionFree R (integralClosure R E) :=
      (Module.isTorsionFree_iff_algebraMap_injective).mpr
        (Motivic.CompleteDVRExtension.integralClosure_algebraMap_injective R F E)
    ∀ {π : R} {ϖ : integralClosure R E} (_ : Irreducible π) (_ : Irreducible ϖ)
      (u : (integralClosure R E)ˣ) (e : ℕ),
      algebraMap R (integralClosure R E) π = (u : integralClosure R E) * ϖ ^ e →
      Module.finrank (ResidueField R) (ResidueField (integralClosure R E)) = 1 →
      ∃ b : Rˣ, Algebra.intNorm R (integralClosure R E) ϖ = π * (b : R) ∧
        residue R (b : R) = (-1 : ResidueField R) ^ (e - 1) *
          (Algebra.norm (ResidueField R)
            (residue (integralClosure R E) (u : integralClosure R E)))⁻¹ := by
  let S := integralClosure R E
  let : IsDiscreteValuationRing S :=
    Motivic.CompleteDVRExtension.integralClosure_isDiscreteValuationRing R F E
  let : HenselianLocalRing S :=
    Motivic.CompleteDVRExtension.integralClosure_henselianLocalRing R F E
  let : IsLocalHom (algebraMap R S) :=
    Motivic.CompleteDVRExtension.integralClosure_isLocalHom R F E
  let : IsFractionRing S E := IsIntegralClosure.isFractionRing_of_finite_extension R F E S
  let : Module.Finite R S := IsIntegralClosure.finite R F E S
  let : Module.IsTorsionFree R S := (Module.isTorsionFree_iff_algebraMap_injective).mpr
    (Motivic.CompleteDVRExtension.integralClosure_algebraMap_injective R F E)
  let : CharZero (ResidueField S) := charZero_of_injective_algebraMap
    (algebraMap (ResidueField R) (ResidueField S)).injective
  dsimp only
  intro π ϖ hπ hϖ u e he hf
  exact residue_characteristic_zero R S F E hπ hϖ u e he hf

end Complete

end MotivicTest.DVRUniformizerNorm

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let native :=
    #[`IsDiscreteValuationRing.exists_uniformizer_norm_coefficient_of_residue_finrank_one]
  let selected (name : Name) := native.contains name ||
    (`MotivicTest.DVRUniformizerNorm).isPrefixOf name
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
  logInfo m!"Checked {names.size} exact uniformizer-norm declarations: standard axioms only."
