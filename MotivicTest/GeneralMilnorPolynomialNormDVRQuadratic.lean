/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.KTheory.MilnorK.PolynomialNormDVRQuadratic
import Lean.Util.CollectAxioms

/-! All-class quadratic norm–residue consumers, including arbitrary higher-degree
classes and signed combinations of extension-field symbols with no base-field
prefix requirement. No canonical norm or tower law is assumed. -/

open Polynomial Polynomial.LocalResidue IsLocalRing
open Motivic.KTheory MilnorK MilnorK.PolynomialResidue MilnorK.PolynomialNorm

namespace MotivicTest.GeneralMilnorPolynomialNormDVRQuadratic

section ActualExtension

variable (R F : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Algebra R F] [IsFractionRing R F] [CharZero F]
  (p : MonicIrreducible F)
  (S : Type*) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [HenselianLocalRing S] [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [IsLocalHom (algebraMap R S)] [CharZero (ResidueField R)]
  [Algebra S (AdjoinRoot p.val)] [IsScalarTower R S (AdjoinRoot p.val)]
  [IsFractionRing S (AdjoinRoot p.val)] [IsIntegralClosure S R (AdjoinRoot p.val)]
  {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
  (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
  (heunit : IsUnit (e : S)) (hp : p.val.natDegree = 2)
  (q : MonicIrreducible (ResidueField R))
  (ε : AdjoinRoot q.val ≃ₐ[ResidueField R] ResidueField S)

include hπ hϖ he heunit hp

/-- The input is an arbitrary class of the original extension-field quotient. -/
theorem all_classes (n : ℕ) (z : K (AdjoinRoot p.val) (n + 1)) :
    DVR.residue R F n (polynomialNorm (n + 1) p z) =
      polynomialNorm n q (map n ε.symm.toRingHom
        (DVR.residue S (AdjoinRoot p.val) n z)) :=
  residue_polynomialNorm_quadratic R F p S n z hp hπ hϖ u e he heunit q ε

/-- Neither symbol is required to have any coordinate in the base field. -/
theorem signed_extension_symbols (n : ℕ)
    (a b : SymbolTuple (AdjoinRoot p.val) (n + 1)) :
    DVR.residue R F n (polynomialNorm (n + 1) p
      ((-3 : ℤ) • symbol a + (5 : ℤ) • symbol b)) =
      polynomialNorm n q (map n ε.symm.toRingHom
        (DVR.residue S (AdjoinRoot p.val) n
          ((-3 : ℤ) • symbol a + (5 : ℤ) • symbol b))) :=
  all_classes R F p S hπ hϖ u e he heunit hp q ε n _

/-- The all-class degree-one square retains the original degree-zero norm. -/
theorem degree_one (z : K (AdjoinRoot p.val) 1) :
    DVR.residue R F 0 (polynomialNorm 1 p z) =
      polynomialNorm 0 q (map 0 ε.symm.toRingHom
        (DVR.residue S (AdjoinRoot p.val) 0 z)) :=
  all_classes R F p S hπ hϖ u e he heunit hp q ε 0 z

/-- The old tame map is recovered for an arbitrary quadratic-extension K₂ class. -/
theorem original_K2_tame (z : K (AdjoinRoot p.val) 2) :
    MilnorK2.tame (MilnorK2.DVR.chosenData R F)
      (twoEquiv F (polynomialNorm 2 p z)) =
      oneEquiv (ResidueField R) (polynomialNorm 1 q (map 1 ε.symm.toRingHom
        (DVR.residue S (AdjoinRoot p.val) 1 z))) := by
  rw [← DVR.oneEquiv_residue_one]
  exact congrArg (oneEquiv (ResidueField R))
    (all_classes R F p S hπ hϖ u e he heunit hp q ε 1 z)

end ActualExtension

end MotivicTest.GeneralMilnorPolynomialNormDVRQuadratic

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`Motivic.KTheory.MilnorK,
    `MotivicTest.GeneralMilnorPolynomialNormDVRQuadratic]
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
  logInfo m!"Checked {names.size} quadratic norm–residue and Milnor declarations: \
    standard axioms only."
