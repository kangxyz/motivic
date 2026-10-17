/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.KTheory.MilnorK.PolynomialNormDVRPGroupDescent
import Lean.Util.CollectAxioms

/-! Actual degree annihilator, with no residue-law or branch-count premise. -/

namespace MotivicTest.GeneralMilnorDVRWeightedDescent

open Motivic.KTheory.MilnorK Polynomial PolynomialResidue PolynomialNorm
  Polynomial.LocalResidue AdjoinRoot IsLocalRing

attribute [local instance] Motivic.KTheory.MilnorK.rootFinite

universe u

/-- The restricted residue of the original norm is the full upper branch sum,
with each original vertical ramification exponent visible. -/
theorem actual_degree_annihilator_from_all_branches
    {F L : Type u} [Field F] [CharZero F] [Field L] [CharZero L]
    [Algebra F L] [FiniteDimensional F L]
    (R S T : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R F] [IsFractionRing R F] [CharZero (ResidueField R)]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [IsAdicComplete (maximalIdeal T) T] [CharZero (ResidueField T)]
    [Algebra R T] [IsLocalHom (algebraMap R T)]
    [Module.Finite R T] [Module.IsTorsionFree R T]
    [Algebra T L] [IsFractionRing T L] [Algebra R L]
    [IsScalarTower R F L] [IsScalarTower R T L] [IsIntegralClosure T R L]
    (p : MonicIrreducible F)
    [Algebra S (AdjoinRoot p.val)] [IsFractionRing S (AdjoinRoot p.val)]
    [Algebra R S] [IsScalarTower R S (AdjoinRoot p.val)]
    [Module.Finite R S] [Module.IsTorsionFree R S] [IsIntegralClosure S R (AdjoinRoot p.val)]
    [IsLocalHom (algebraMap R S)]
    (U : IrreducibleBranch (p.val.map (algebraMap F L)) → Type u)
    [∀ r, CommRing (U r)] [∀ r, IsDomain (U r)] [∀ r, IsDiscreteValuationRing (U r)]
    [∀ r, Algebra T (U r)] [∀ r, Module.Finite T (U r)]
    [∀ r, Module.IsTorsionFree T (U r)]
    [∀ r, Algebra S (U r)] [∀ r, Algebra R (U r)]
    [∀ r, IsScalarTower R S (U r)] [∀ r, IsScalarTower R T (U r)]
    [∀ r, IsLocalHom (algebraMap S (U r))] [∀ r, IsLocalHom (algebraMap R (U r))]
    [∀ r, IsLocalHom (algebraMap T (U r))]
    [∀ r, Algebra (U r) (AdjoinRoot r.val.val)]
    [∀ r, IsScalarTower T (U r) (AdjoinRoot r.val.val)]
    [∀ r, IsFractionRing (U r) (AdjoinRoot r.val.val)]
    [∀ r, IsIntegralClosure (U r) T (AdjoinRoot r.val.val)]
    (Ω : Type u) [Field Ω] [Algebra L Ω] [FiniteDimensional L Ω] [IsGalois L Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (hG : IsPGroup ℓ (Ω ≃ₐ[L] Ω))
    (g : ∀ r : IrreducibleBranch (p.val.map (algebraMap F L)),
      AdjoinRoot r.val.val →ₐ[L] Ω)
    (hj : ∀ r s, adjoinRootMap (algebraMap F L) p.val r.val.val r.property
      (algebraMap S (AdjoinRoot p.val) s) =
        algebraMap (U r) (AdjoinRoot r.val.val) (algebraMap S (U r) s))
    {π : R} {ϖ : S} {τ : T}
    (hπ : Irreducible π) (hϖ : Irreducible ϖ) (hτ : Irreducible τ)
    (ρ : ∀ r, U r) (hρ : ∀ r, Irreducible (ρ r))
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
    (v : Tˣ) (a : ℕ) (ha : algebraMap R T π = (v : T) * τ ^ a)
    (w z : ∀ r, (U r)ˣ) (b c : IrreducibleBranch (p.val.map (algebraMap F L)) → ℕ)
    (hb : ∀ r, algebraMap S (U r) ϖ = (w r : U r) * ρ r ^ b r)
    (hc : ∀ r, algebraMap T (U r) τ = (z r : U r) * ρ r ^ c r)
    (n : ℕ) (x : K (AdjoinRoot p.val) (n + 1)) :
    Module.finrank F L •
      (DVR.residue R F n (polynomialNorm (n + 1) p x) -
        finiteExtensionNorm (ResidueField R) (ResidueField S) n
          (DVR.residue S (AdjoinRoot p.val) n x)) = 0 :=
  degree_smul_normResidue_defect_eq_zero_of_pGroup_branches R S T p U Ω ℓ hG g hj
    hπ hϖ hτ ρ hρ u e he v a ha w z b c hb hc n x

end MotivicTest.GeneralMilnorDVRWeightedDescent

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`AdjoinRoot, `Motivic.KTheory.MilnorK,
    `MotivicTest.GeneralMilnorDVRWeightedDescent]
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
  logInfo m!"Checked {names.size} DVR weighted descent and Milnor declarations: \
    standard axioms only."
