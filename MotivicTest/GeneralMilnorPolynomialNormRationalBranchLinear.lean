/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.KTheory.MilnorK.PolynomialNormRationalBranchLinear
import Lean.Util.CollectAxioms

/-! The actual linear-place square for linear presentations and every member
of the full coefficient branch set of a prime-normal presentation. -/

open Polynomial Polynomial.LocalResidue AdjoinRoot
open Motivic.KTheory.MilnorK Motivic.KTheory.MilnorK.PolynomialResidue
open Motivic.KTheory.MilnorK.PolynomialNorm

namespace MotivicTest.GeneralMilnorPolynomialNormRationalBranchLinear

variable {k H : Type*} [Field k] [Field H]

local instance (a : k) : Fact (Irreducible (X - C a)) := ⟨irreducible_X_sub_C a⟩
local instance (p : MonicIrreducible k) (a : AdjoinRoot p.val) :
    Fact (Irreducible (X - C a)) := ⟨irreducible_X_sub_C a⟩

/-- The degree-one case is at an arbitrary original linear place, rather
than only the place zero or the residue at infinity. -/
theorem actual_linear_presentation [CharZero k]
    (p : MonicIrreducible k) (hp : p.val.natDegree = 1) (a : k) (n : ℕ)
    (x : K (RatFunc (AdjoinRoot p.val)) (n + 1)) :
    map n (linearRootEquiv a).toRingHom
      (residueAt (X - C a) n (rationalFunctionNorm (n + 1) p x)) =
      polynomialNorm n p
        (map n (linearRootEquiv (algebraMap k (AdjoinRoot p.val) a)).toRingHom
          (residueAt (X - C (algebraMap k (AdjoinRoot p.val) a)) n x)) :=
  residueAt_linear_rationalFunctionNorm_linear p hp a n x

/-- Every index in the full norm base-change sum has the required square,
without any assumed branch normality or branch degree. -/
theorem every_placesAbove_square [CharZero k] [Algebra k H]
    (p : MonicIrreducible k) [Normal k (AdjoinRoot p.val)]
    (hp : p.val.natDegree.Prime) (q : {q // q ∈ placesAbove (algebraMap k H) p})
    (a : H) (n : ℕ) (x : K (RatFunc (AdjoinRoot q.val.val)) (n + 1)) :
    map n (linearRootEquiv a).toRingHom
      (residueAt (X - C a) n (rationalFunctionNorm (n + 1) q.val x)) =
      polynomialNorm n q.val
        (map n (linearRootEquiv (algebraMap H (AdjoinRoot q.val.val) a)).toRingHom
          (residueAt (X - C (algebraMap H (AdjoinRoot q.val.val) a)) n x)) :=
  residueAt_linear_rationalFunctionNorm_scalarBranch p hp
    ⟨q.val, (mem_placesAbove _ p q.val).mp q.property⟩ a n x

end MotivicTest.GeneralMilnorPolynomialNormRationalBranchLinear

open Lean in
run_cmd do
  let env ← getEnv
  let names := #[
    `Motivic.KTheory.MilnorK.PolynomialNorm.residueAt_linear_rationalFunctionNorm_linear,
    `Motivic.KTheory.MilnorK.PolynomialNorm.scalarBranch_natDegree_eq_one_or_prime,
    `Motivic.KTheory.MilnorK.PolynomialNorm.residueAt_linear_rationalFunctionNorm_scalarBranch,
    `MotivicTest.GeneralMilnorPolynomialNormRationalBranchLinear.actual_linear_presentation,
    `MotivicTest.GeneralMilnorPolynomialNormRationalBranchLinear.every_placesAbove_square]
  for name in names do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Checked every actual scalar-branch linear norm square: standard axioms only."
