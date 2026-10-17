/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Motivic.Aglib.LinearAlgebra.Dual.ProjectiveBaseChange
import Mathlib.Data.ZMod.Basic
import Lean.Util.CollectAxioms

/-! # Direct tests for original dual detection over arbitrary base algebras -/

public section

open TensorProduct

namespace MotivicTest.ProjectiveDualBaseChange

/-- Direct use with an arbitrary commutative base algebra and a finite projective module, without
adding freeness, flatness, reducedness, or residue-field assumptions. -/
theorem arbitrary_algebra {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    (z : A ⊗[R] M) :
    (∀ φ : Module.Dual R M, φ.baseChange A z = 0) ↔ z = 0 :=
  Module.Dual.forall_baseChange_apply_eq_zero_iff z

/-- The result also applies to the nonflat, nonreduced integer algebra `ZMod 4`. -/
theorem modulo_four {M : Type*} [AddCommGroup M] [Module ℤ M]
    [Module.Finite ℤ M] [Module.Projective ℤ M] (z : ZMod 4 ⊗[ℤ] M) :
    (∀ φ : Module.Dual ℤ M, φ.baseChange (ZMod 4) z = 0) ↔ z = 0 :=
  Module.Dual.forall_baseChange_apply_eq_zero_iff z

example : (2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4) ^ 2 = 0 := by decide

/-- Two base-changed vectors agree if all original dual evaluations agree. -/
theorem original_duals_separate {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    (x y : A ⊗[R] M) (h : ∀ φ : Module.Dual R M, φ.baseChange A x = φ.baseChange A y) :
    x = y := by
  apply sub_eq_zero.mp
  apply (Module.Dual.forall_baseChange_apply_eq_zero_iff (x - y)).mp
  intro φ
  simp [h φ]

end MotivicTest.ProjectiveDualBaseChange

open Lean in
run_cmd do
  for name in #[
      ``Module.Dual.baseChange_dualTensorHom_tmul_apply,
      ``Module.Dual.forall_baseChange_apply_eq_zero_iff,
      ``MotivicTest.ProjectiveDualBaseChange.arbitrary_algebra,
      ``MotivicTest.ProjectiveDualBaseChange.modulo_four,
      ``MotivicTest.ProjectiveDualBaseChange.original_duals_separate] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Finite-projective dual detection after arbitrary base change: standard axioms only."
