/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.KTheory.MilnorK.PolynomialNormDVRUnits
import Motivic.Aglib.RingTheory.CompleteDVRExtension
import Lean.Util.CollectAxioms

/-! Direct consumers of the full degree-one and higher local-unit mixed
norm–residue square. Residue characteristic is unrestricted and every bottom
polynomial is accompanied by an actual residue-field algebra equivalence. -/

open Polynomial Polynomial.LocalResidue IsLocalRing
open Motivic.KTheory MilnorK MilnorK.PolynomialResidue MilnorK.PolynomialNorm

namespace MotivicTest.GeneralMilnorPolynomialNormDVRUnits

section IntegralClosure

variable (R F : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Algebra R F] [IsFractionRing R F] [CharZero F]
  (p : MonicIrreducible F)
  (S : Type*) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [Algebra S (AdjoinRoot p.val)] [IsScalarTower R S (AdjoinRoot p.val)]
  [IsFractionRing S (AdjoinRoot p.val)] [IsIntegralClosure S R (AdjoinRoot p.val)]

/-- The full degree-one equality acts on an arbitrary original Milnor class. -/
theorem arbitrary_degree_one (q : MonicIrreducible (ResidueField R))
    (ε : AdjoinRoot q.val ≃ₐ[ResidueField R] ResidueField S)
    (x : K (AdjoinRoot p.val) 1) :
    DVR.residue R F 0 (polynomialNorm 1 p x) =
      polynomialNorm 0 q (map 0 ε.symm.toRingHom
        (DVR.residue S (AdjoinRoot p.val) 0 x)) :=
  residue_polynomialNorm_one_eq R F p S q ε x

/-- Negative orders are retained literally, without replacing units by integral elements. -/
theorem negative_extension_pole (m : ℕ) (a : Fin m → Rˣ)
    {ϖ : S} (hϖ : Irreducible ϖ) :
    DVR.residue R F m (polynomialNorm (m + 1) p (symbol (Fin.snoc
      (Units.map (algebraMap F (AdjoinRoot p.val)).toMonoidHom ∘
        (MilnorK2.DVR.fieldUnits R F ∘ a))
      (MilnorK2.DVR.uniformizer (K := AdjoinRoot p.val) hϖ ^ (-3 : ℤ))))) =
      ((Module.finrank (ResidueField R) (ResidueField S) : ℤ) * (-3)) •
        symbol (Units.map (IsLocalRing.residue R).toMonoidHom ∘ a) := by
  rw [residue_polynomialNorm_ring_units R F p S]
  simp only [ofMul_zpow, map_smul, MilnorK2.DVR.value_uniformizer, smul_eq_mul, mul_one]

/-- Sign-unit prefixes are allowed in every degree and their residues are not erased. -/
theorem sign_prefix (m : ℕ) (b : (AdjoinRoot p.val)ˣ)
    (q : MonicIrreducible (ResidueField R))
    (ε : AdjoinRoot q.val ≃ₐ[ResidueField R] ResidueField S) :
    DVR.residue R F m (polynomialNorm (m + 1) p (symbol (Fin.snoc
      (Units.map (algebraMap F (AdjoinRoot p.val)).toMonoidHom ∘
        (MilnorK2.DVR.fieldUnits R F ∘ (fun _ : Fin m => (-1 : Rˣ)))) b))) =
      polynomialNorm m q (map m ε.symm.toRingHom
        (DVR.residue S (AdjoinRoot p.val) m (symbol (Fin.snoc
          (Units.map (algebraMap F (AdjoinRoot p.val)).toMonoidHom ∘
            (MilnorK2.DVR.fieldUnits R F ∘ (fun _ : Fin m => (-1 : Rˣ)))) b)))) :=
  residue_polynomialNorm_ring_units_eq R F p S m (fun _ => -1) b q ε

end IntegralClosure

section Complete

variable (R F : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R]
  [Field F] [Algebra R F] [IsFractionRing R F] [CharZero F]

/-- Completeness constructs the actual source DVR and its finite residue
extension; the residue primitive presentation still remains explicit. -/
theorem actual_complete_DVR_square (p : MonicIrreducible F) :
    let _ := (AdjoinRoot.powerBasis p.property.2.ne_zero).finite
    let _ := Motivic.CompleteDVRExtension.integralClosure_isDiscreteValuationRing
      R F (AdjoinRoot p.val)
    let _ := Motivic.CompleteDVRExtension.integralClosure_isLocalHom R F (AdjoinRoot p.val)
    let _ := IsIntegralClosure.isFractionRing_of_finite_extension
      R F (AdjoinRoot p.val) (integralClosure R (AdjoinRoot p.val))
    ∀ (m : ℕ) (a : Fin m → Rˣ) (b : (AdjoinRoot p.val)ˣ)
      (q : MonicIrreducible (ResidueField R))
      (ε : AdjoinRoot q.val ≃ₐ[ResidueField R]
        ResidueField (integralClosure R (AdjoinRoot p.val))),
    DVR.residue R F m (polynomialNorm (m + 1) p (symbol (Fin.snoc
      (Units.map (algebraMap F (AdjoinRoot p.val)).toMonoidHom ∘
        (MilnorK2.DVR.fieldUnits R F ∘ a)) b))) =
      polynomialNorm m q (map m ε.symm.toRingHom
        (DVR.residue (integralClosure R (AdjoinRoot p.val)) (AdjoinRoot p.val) m
          (symbol (Fin.snoc (Units.map (algebraMap F (AdjoinRoot p.val)).toMonoidHom ∘
            (MilnorK2.DVR.fieldUnits R F ∘ a)) b)))) := by
  let : FiniteDimensional F (AdjoinRoot p.val) :=
    (AdjoinRoot.powerBasis p.property.2.ne_zero).finite
  let S := integralClosure R (AdjoinRoot p.val)
  let : IsDiscreteValuationRing S :=
    Motivic.CompleteDVRExtension.integralClosure_isDiscreteValuationRing R F (AdjoinRoot p.val)
  let : IsLocalHom (algebraMap R S) :=
    Motivic.CompleteDVRExtension.integralClosure_isLocalHom R F (AdjoinRoot p.val)
  let : IsFractionRing S (AdjoinRoot p.val) :=
    IsIntegralClosure.isFractionRing_of_finite_extension R F (AdjoinRoot p.val) S
  let : Module.Finite R S := IsIntegralClosure.finite R F (AdjoinRoot p.val) S
  let : Module.IsTorsionFree R S := (Module.isTorsionFree_iff_algebraMap_injective).mpr
    (Motivic.CompleteDVRExtension.integralClosure_algebraMap_injective R F (AdjoinRoot p.val))
  dsimp only
  intro m a b q ε
  exact residue_polynomialNorm_ring_units_eq R F p S m a b q ε

end Complete

end MotivicTest.GeneralMilnorPolynomialNormDVRUnits

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`Motivic.KTheory.MilnorK, `MotivicTest.GeneralMilnorPolynomialNormDVRUnits,
    `Motivic.DVRNormValuation, `Motivic.CompleteDVRExtension]
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
  logInfo m!"Checked {names.size} mixed-unit norm–residue and dependency declarations: \
    standard axioms only."
