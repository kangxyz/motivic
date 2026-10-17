/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Dual.BaseChange

/-!
# Original duals detect zero after arbitrary base change

For a finite projective module, the base changes of its original dual functionals jointly detect
zero over every algebra. No flatness, reducedness, field, or global freeness hypothesis is needed.
The proof lifts the identity endomorphism through the finite-projective contraction equivalence.
-/

public section

open TensorProduct

namespace Module.Dual

variable {R A M : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  [AddCommMonoid M] [Module R M]

/-- Base change of a rank-one endomorphism evaluates its original dual and reconstructs the
corresponding multiple of its vector. -/
theorem baseChange_dualTensorHom_tmul_apply (φ : Dual R M) (m : M) (z : A ⊗[R] M) :
    (dualTensorHom R M M (φ ⊗ₜ[R] m)).baseChange A z =
      φ.baseChange A z • ((1 : A) ⊗ₜ[R] m) := by
  induction z using TensorProduct.inductionOn with
  | tmul a n =>
    simp [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  | add x y hx hy => simp [hx, hy, add_smul]

/-- Original dual functionals jointly detect zero after arbitrary base change of a finite
projective module. The algebra is not assumed flat, reduced, or a field. -/
theorem forall_baseChange_apply_eq_zero_iff [Module.Finite R M] [Module.Projective R M]
    (z : A ⊗[R] M) : (∀ φ : Dual R M, φ.baseChange A z = 0) ↔ z = 0 := by
  constructor
  · intro hz
    have h (t : Dual R M ⊗[R] M) : (dualTensorHom R M M t).baseChange A z = 0 := by
      induction t using TensorProduct.inductionOn with
      | tmul φ m => rw [baseChange_dualTensorHom_tmul_apply, hz φ, zero_smul]
      | add x y hx hy => simp [hx, hy]
    obtain ⟨t, ht⟩ := (dualTensorHom_bijective (R := R) (M := M) (N := M)).surjective
      LinearMap.id
    simpa [ht] using h t
  · rintro rfl φ
    exact map_zero _

end Module.Dual
