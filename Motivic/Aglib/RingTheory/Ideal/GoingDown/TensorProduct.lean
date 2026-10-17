/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Ideal.GoingDown.Equiv
public import Motivic.Aglib.RingTheory.Ideal.GoingDown.Quotient
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Tensor-product going down through quotients and surjections

Going down for an actual tensor product descends through any quotient or
surjective algebra presentation of its left factor. The proofs retain the
canonical tensor-quotient and tensor-product equivalences and their scalar maps.

## Upstream candidate

Intended upstream module: `Aglib.RingTheory.Ideal.GoingDown.TensorProduct`.
The four commutative rings may occupy independent universes. Only going down
for the original tensor product is required; there is no domain, normality,
integrality, flatness, reducedness or finiteness assumption. The current
consumer is `Motivic.Aglib.RingTheory.Ideal.GoingDown.BaseChange`.

Extracted from `Motivic.RingTheory.GoingDown.BaseChange`, source SHA-256
`adf1dd2b2b356e30e7ae322da32387dce5edfb681dc840cfbd22ea1c3b67ed6e`.
-/

@[expose] public section

open scoped TensorProduct

universe u v w x

namespace Algebra.HasGoingDown

variable {R : Type u} {S : Type v} {P : Type w} {A : Type x}
  [CommRing R] [CommRing S] [CommRing P] [CommRing A]

/-- Going down for an actual tensor product descends through a quotient of
its left factor, using the canonical tensor-quotient equivalence. -/
theorem tensor_quotient [Algebra R S] [Algebra R P]
    [Algebra.HasGoingDown P (P ⊗[R] S)] (I : Ideal P) :
    Algebra.HasGoingDown (P ⧸ I) ((P ⧸ I) ⊗[R] S) := by
  have := Algebra.HasGoingDown.quotient_map (S := P ⊗[R] S) I
  let e := Algebra.TensorProduct.quotientTensorEquiv (R := R) R S P I
  apply Algebra.HasGoingDown.of_equivalences (RingEquiv.refl (P ⧸ I)) e.symm.toRingEquiv
  apply RingHom.ext
  intro q
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  change e.symm (Ideal.Quotient.mk _ (p ⊗ₜ[R] (1 : S))) =
    Ideal.Quotient.mk I p ⊗ₜ[R] (1 : S)
  exact Algebra.TensorProduct.quotientTensorEquiv_symm_apply_tmul (R := R) R S P I p 1

/-- A surjective algebra presentation transports tensor-product going down
to the presented algebra, without any domain assumption on that algebra. -/
theorem tensor_of_surjective [Algebra R S] [Algebra R P] [Algebra R A]
    [Algebra.HasGoingDown P (P ⊗[R] S)] (f : P →ₐ[R] A) (hf : Function.Surjective f) :
    Algebra.HasGoingDown A (A ⊗[R] S) := by
  have := tensor_quotient (R := R) (S := S) (RingHom.ker f)
  let e := Ideal.quotientKerAlgEquivOfSurjective hf
  let eT := Algebra.TensorProduct.congr e (AlgEquiv.refl : S ≃ₐ[R] S)
  apply Algebra.HasGoingDown.of_equivalences e.toRingEquiv eT.toRingEquiv
  apply RingHom.ext
  intro q
  change eT (q ⊗ₜ[R] (1 : S)) = e q ⊗ₜ[R] (1 : S)
  simp [eT]

end Algebra.HasGoingDown
