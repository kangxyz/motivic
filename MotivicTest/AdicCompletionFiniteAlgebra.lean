/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.Aglib.RingTheory.AdicCompletion.FiniteRank
import Aglib.RingTheory.AdicCompletion.Powers
import Lean.Util.CollectAxioms

/-! The finite tensor comparison is an actual unital algebra equivalence. -/

open TensorProduct

namespace MotivicTest.AdicCompletionFiniteAlgebra

universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [IsNoetherianRing R] [Module.Finite R S] (I : Ideal R)

/-- The original integral algebra enters through its actual completion map. -/
theorem actual_coefficients (s : S) :
    AdicCompletion.tensorEquivExtendedCompletion I (1 ⊗ₜ[R] s) =
      algebraMap S (AdicCompletion (I.map (algebraMap R S)) S) s :=
  AdicCompletion.tensorEquivExtendedCompletion_one_tmul I s

/-- Multiplicativity is proved, not supplied as a branch-identification hypothesis. -/
theorem actual_multiplication (x y : AdicCompletion I R ⊗[R] S) :
    AdicCompletion.tensorEquivExtendedCompletion I (x * y) =
      AdicCompletion.tensorEquivExtendedCompletion I x *
        AdicCompletion.tensorEquivExtendedCompletion I y :=
  map_mul _ x y

end MotivicTest.AdicCompletionFiniteAlgebra

open Lean in
run_cmd do
  let env ← getEnv
  let names := #[`AdicCompletion.finrank_extendedCompletion, `AdicCompletion.powAlgEquiv,
    `AdicCompletion.mapIdealLinearEquiv,
    `AdicCompletion.tensorEquivExtendedCompletion,
    `AdicCompletion.tensorEquivExtendedCompletionBase,
    `MotivicTest.AdicCompletionFiniteAlgebra.actual_coefficients,
    `MotivicTest.AdicCompletionFiniteAlgebra.actual_multiplication]
  for name in names do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual finite algebra completion: transitive standard axioms only."
