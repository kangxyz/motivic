/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.KTheory.MilnorK.PolynomialNormPrimeNormal
import Motivic.KTheory.MilnorK.PolynomialNormCompatibility
import Lean.Util.CollectAxioms

/-! Direct consumers of actual common-splitting comparison and prime-normal
presentation independence, with degree zero, original degree two, and a
quadratic instance where normality is genuinely supplied by Mathlib. -/

open Polynomial Polynomial.LocalResidue
open Motivic.KTheory MilnorK MilnorK.PolynomialResidue MilnorK.PolynomialNorm

namespace MotivicTest.GeneralMilnorPolynomialNormPrimeNormal

variable {k L : Type*} [Field k] [Field L]

/-- The exact common-splitting equality requires neither finite L nor normality. -/
theorem common_splitting_field [CharZero k] [Algebra k L]
    (n : ℕ) (p q : MonicIrreducible k) (e : AdjoinRoot p.val ≃ₐ[k] AdjoinRoot q.val)
    (hp : (p.val.map (algebraMap k L)).Splits)
    (hq : (q.val.map (algebraMap k L)).Splits) (x : K (AdjoinRoot p.val) n) :
    map n (algebraMap k L) (polynomialNorm n q (map n e.toRingHom x)) =
      map n (algebraMap k L) (polynomialNorm n p x) :=
  polynomialNorm_restrict_map_algEquiv_of_splits n p q e hp hq x

/-- K₀ is multiplication by the actual polynomial degree, in arbitrary characteristic. -/
theorem degree_zero_normalization (p : MonicIrreducible k) (x : K (AdjoinRoot p.val) 0) :
    zeroEquiv k (polynomialNorm 0 p x) =
      (p.val.natDegree : ℤ) * zeroEquiv (AdjoinRoot p.val) x :=
  zeroEquiv_polynomialNorm p x

/-- K₀ presentation independence needs neither prime degree nor normality. -/
theorem degree_zero_independence (p q : MonicIrreducible k)
    (e : AdjoinRoot p.val ≃ₐ[k] AdjoinRoot q.val) (x : K (AdjoinRoot p.val) 0) :
    polynomialNorm 0 q (map 0 e.toRingHom x) = polynomialNorm 0 p x :=
  polynomialNorm_zero_map_algEquiv p q e x

/-- The prime-normal theorem acts on every class in every Milnor degree. -/
theorem all_degrees [CharZero k] (n : ℕ) (p q : MonicIrreducible k)
    (hp : p.val.natDegree.Prime) [Normal k (AdjoinRoot p.val)]
    (e : AdjoinRoot p.val ≃ₐ[k] AdjoinRoot q.val) (x : K (AdjoinRoot p.val) n) :
    polynomialNorm n q (map n e.toRingHom x) = polynomialNorm n p x :=
  polynomialNorm_map_algEquiv_of_prime_normal n p q hp e x

/-- The equality is genuinely an equality of the two integer-linear maps. -/
theorem actual_linear_maps [CharZero k] (n : ℕ) (p q : MonicIrreducible k)
    (hp : p.val.natDegree.Prime) [Normal k (AdjoinRoot p.val)]
    (e : AdjoinRoot p.val ≃ₐ[k] AdjoinRoot q.val) :
    (polynomialNorm n q).comp (map n e.toRingHom) = polynomialNorm n p := by
  apply LinearMap.ext
  intro x
  exact polynomialNorm_map_algEquiv_of_prime_normal n p q hp e x

/-- The result agrees with the original K₂ polynomial norms and actual K₂ map. -/
theorem original_degree_two [CharZero k] (p q : MonicIrreducible k)
    (hp : p.val.natDegree.Prime) [Normal k (AdjoinRoot p.val)]
    (e : AdjoinRoot p.val ≃ₐ[k] AdjoinRoot q.val)
    (z : MilnorK2.K2 (AdjoinRoot p.val)) :
    MilnorK3.PolynomialNorm.polynomialNorm q (MilnorK2.map e.toRingHom z) =
      MilnorK3.PolynomialNorm.polynomialNorm p z := by
  have h := congrArg (twoEquiv k)
    (polynomialNorm_map_algEquiv_of_prime_normal 2 p q hp e ((twoEquiv _).symm z))
  simpa only [twoEquiv_polynomialNorm, twoEquiv_map, LinearEquiv.apply_symm_apply] using h

/-- For quadratic extensions normality is derived from the actual degree-two
field instance and separability, rather than inferred from arbitrary prime degree. -/
theorem quadratic [CharZero k] (n : ℕ) (p q : MonicIrreducible k)
    (hp : p.val.natDegree = 2) (e : AdjoinRoot p.val ≃ₐ[k] AdjoinRoot q.val)
    (x : K (AdjoinRoot p.val) n) :
    polynomialNorm n q (map n e.toRingHom x) = polynomialNorm n p x := by
  let : FiniteDimensional k (AdjoinRoot p.val) := p.property.1.finite_adjoinRoot
  let : Algebra.IsQuadraticExtension k (AdjoinRoot p.val) :=
    { finrank_eq_two' := by
        rw [(AdjoinRoot.powerBasis p.property.2.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hp] }
  exact polynomialNorm_map_algEquiv_of_prime_normal n p q (hp ▸ Nat.prime_two) e x

end MotivicTest.GeneralMilnorPolynomialNormPrimeNormal

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`Motivic.KTheory.MilnorK, `MotivicTest.GeneralMilnorPolynomialNormPrimeNormal]
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
  logInfo m!"Checked {names.size} prime-normal and general Milnor declarations: \
    standard axioms only."
