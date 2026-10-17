/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.KTheory.MilnorK.PolynomialNormDVRUniformizer
import Motivic.Aglib.RingTheory.CompleteDVRExtension
import Lean.Util.CollectAxioms

/-! Direct prime-degree mixed norm–residue consumers include arbitrary prefix
classes, repeated base poles, a final extension pole, the literal empty prefix,
the original K₂ tame map, and an actual complete-DVR integral closure. -/

open Polynomial Polynomial.LocalResidue IsLocalRing
open Motivic.KTheory MilnorK MilnorK.PolynomialResidue MilnorK.PolynomialNorm

namespace MotivicTest.GeneralMilnorPolynomialNormDVRUniformizer

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
  (heunit : IsUnit (e : S)) (hp : Nat.Prime p.val.natDegree)
  (q : MonicIrreducible (ResidueField R))
  (ε : AdjoinRoot q.val ≃ₐ[ResidueField R] ResidueField S)

include hπ hϖ he heunit hp

/-- An arbitrary original base class precedes the actual extension uniformizer. -/
theorem final_uniformizer (n : ℕ) (x : K F n) :
    DVR.residue R F n (polynomialNorm (n + 1) p
      (productUnit n (map n (algebraMap F (AdjoinRoot p.val)) x)
        (Additive.ofMul (MilnorK2.DVR.uniformizer (K := AdjoinRoot p.val) hϖ)))) =
      polynomialNorm n q (map n ε.symm.toRingHom
        (DVR.residue S (AdjoinRoot p.val) n
          (productUnit n (map n (algebraMap F (AdjoinRoot p.val)) x)
            (Additive.ofMul (MilnorK2.DVR.uniformizer (K := AdjoinRoot p.val) hϖ))))) :=
  residue_polynomialNorm_final_uniformizer R F p S n x hπ hϖ u e he heunit hp q ε

/-- Every last extension-field unit is allowed, including negative order. -/
theorem arbitrary_mixed (n : ℕ) (x : K F n) (b : (AdjoinRoot p.val)ˣ) :
    DVR.residue R F n (polynomialNorm (n + 1) p
      (productUnit n (map n (algebraMap F (AdjoinRoot p.val)) x) (Additive.ofMul b))) =
      polynomialNorm n q (map n ε.symm.toRingHom
        (DVR.residue S (AdjoinRoot p.val) n
          (productUnit n (map n (algebraMap F (AdjoinRoot p.val)) x) (Additive.ofMul b)))) :=
  residue_polynomialNorm_mixed_prime R F p S n x b hπ hϖ u e he heunit hp q ε

/-- Repeated source poles and a negative final uniformizer power are retained. -/
theorem repeated_poles (n : ℕ) :
    DVR.residue R F n (polynomialNorm (n + 1) p (productUnit n
      (map n (algebraMap F (AdjoinRoot p.val))
        (symbol (fun _ => MilnorK2.DVR.uniformizer (K := F) hπ ^ (-3 : ℤ))))
      (Additive.ofMul (MilnorK2.DVR.uniformizer (K := AdjoinRoot p.val) hϖ ^ (-5 : ℤ))))) =
      polynomialNorm n q (map n ε.symm.toRingHom
        (DVR.residue S (AdjoinRoot p.val) n (productUnit n
          (map n (algebraMap F (AdjoinRoot p.val))
            (symbol (fun _ => MilnorK2.DVR.uniformizer (K := F) hπ ^ (-3 : ℤ))))
          (Additive.ofMul (MilnorK2.DVR.uniformizer (K := AdjoinRoot p.val) hϖ ^ (-5 : ℤ)))))) :=
  arbitrary_mixed R F p S hπ hϖ u e he heunit hp q ε n _ _

/-- The empty prefix is a genuine K₀ class and the resulting square is K₁. -/
theorem empty_prefix (x : K F 0) (b : (AdjoinRoot p.val)ˣ) :
    DVR.residue R F 0 (polynomialNorm 1 p
      (productUnit 0 (map 0 (algebraMap F (AdjoinRoot p.val)) x) (Additive.ofMul b))) =
      polynomialNorm 0 q (map 0 ε.symm.toRingHom
        (DVR.residue S (AdjoinRoot p.val) 0
          (productUnit 0 (map 0 (algebraMap F (AdjoinRoot p.val)) x) (Additive.ofMul b)))) :=
  arbitrary_mixed R F p S hπ hϖ u e he heunit hp q ε 0 x b

/-- Degree two uses the original K₂ tame map after the established equivalence. -/
theorem original_K2_tame (x : K F 1) (b : (AdjoinRoot p.val)ˣ) :
    MilnorK2.tame (MilnorK2.DVR.chosenData R F)
      (twoEquiv F (polynomialNorm 2 p
        (productUnit 1 (map 1 (algebraMap F (AdjoinRoot p.val)) x) (Additive.ofMul b)))) =
      oneEquiv (ResidueField R) (polynomialNorm 1 q (map 1 ε.symm.toRingHom
        (DVR.residue S (AdjoinRoot p.val) 1
          (productUnit 1 (map 1 (algebraMap F (AdjoinRoot p.val)) x) (Additive.ofMul b))))) := by
  rw [← DVR.oneEquiv_residue_one]
  exact congrArg (oneEquiv (ResidueField R))
    (arbitrary_mixed R F p S hπ hϖ u e he heunit hp q ε 1 x b)

end ActualExtension

section Complete

variable (R F : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R]
  [Field F] [Algebra R F] [IsFractionRing R F] [CharZero (ResidueField R)]

/-- The actual complete-DVR integral closure supplies Hensel lifting, the
positive uniformizer equation and invertibility through residue characteristic zero. -/
theorem complete_DVR_mixed (p : MonicIrreducible F) (hp : Nat.Prime p.val.natDegree) :
    let _ : CharZero R := RingHom.charZero (residue R)
    let _ : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective R F)
    let _ := (AdjoinRoot.powerBasis p.property.2.ne_zero).finite
    let _ := Motivic.CompleteDVRExtension.integralClosure_isDiscreteValuationRing
      R F (AdjoinRoot p.val)
    let _ := Motivic.CompleteDVRExtension.integralClosure_henselianLocalRing R F (AdjoinRoot p.val)
    let _ := Motivic.CompleteDVRExtension.integralClosure_isLocalHom R F (AdjoinRoot p.val)
    let _ := IsIntegralClosure.isFractionRing_of_finite_extension
      R F (AdjoinRoot p.val) (integralClosure R (AdjoinRoot p.val))
    ∀ (n : ℕ) (x : K F n) (b : (AdjoinRoot p.val)ˣ)
      (q : MonicIrreducible (ResidueField R))
      (ε : AdjoinRoot q.val ≃ₐ[ResidueField R]
        ResidueField (integralClosure R (AdjoinRoot p.val))),
    DVR.residue R F n (polynomialNorm (n + 1) p
      (productUnit n (map n (algebraMap F (AdjoinRoot p.val)) x) (Additive.ofMul b))) =
      polynomialNorm n q (map n ε.symm.toRingHom
        (DVR.residue (integralClosure R (AdjoinRoot p.val)) (AdjoinRoot p.val) n
          (productUnit n (map n (algebraMap F (AdjoinRoot p.val)) x) (Additive.ofMul b)))) := by
  let : CharZero R := RingHom.charZero (residue R)
  let : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective R F)
  let : FiniteDimensional F (AdjoinRoot p.val) :=
    (AdjoinRoot.powerBasis p.property.2.ne_zero).finite
  let S := integralClosure R (AdjoinRoot p.val)
  let : IsDiscreteValuationRing S :=
    Motivic.CompleteDVRExtension.integralClosure_isDiscreteValuationRing R F (AdjoinRoot p.val)
  let : HenselianLocalRing S :=
    Motivic.CompleteDVRExtension.integralClosure_henselianLocalRing R F (AdjoinRoot p.val)
  let : IsLocalHom (algebraMap R S) :=
    Motivic.CompleteDVRExtension.integralClosure_isLocalHom R F (AdjoinRoot p.val)
  let : IsFractionRing S (AdjoinRoot p.val) :=
    IsIntegralClosure.isFractionRing_of_finite_extension R F (AdjoinRoot p.val) S
  let : Module.Finite R S := IsIntegralClosure.finite R F (AdjoinRoot p.val) S
  let : Module.IsTorsionFree R S := (Module.isTorsionFree_iff_algebraMap_injective).mpr
    (Motivic.CompleteDVRExtension.integralClosure_algebraMap_injective R F (AdjoinRoot p.val))
  let : CharZero (ResidueField S) := charZero_of_injective_algebraMap
    (algebraMap (ResidueField R) (ResidueField S)).injective
  dsimp only
  intro n x b q ε
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S
  obtain ⟨e, hepos, u, he⟩ :=
    Motivic.CompleteDVRExtension.integralClosure_exists_positive_ramification
      R F (AdjoinRoot p.val) hπ hϖ
  exact residue_polynomialNorm_mixed_prime R F p S n x b hπ hϖ u e he
    (Motivic.HenselianPrincipalRoots.isUnit_natCast_of_residue_charZero e hepos) hp q ε

end Complete

end MotivicTest.GeneralMilnorPolynomialNormDVRUniformizer

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`Motivic.KTheory.MilnorK,
    `MotivicTest.GeneralMilnorPolynomialNormDVRUniformizer]
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
  logInfo m!"Checked {names.size} prime mixed norm–residue and general Milnor declarations: \
    standard axioms only."
