/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Additivity
public import Aglib.RingTheory.ScalarHomology.BaseChange
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Principal Euler expressions over original quotient scalar rings

Surjective scalar restriction preserves the full kernel and cokernel lengths.
The literal quotient by the scalar-map kernel is identified with the target
ring by the first isomorphism theorem. A principal kernel then supplies the
original scalar cokernel, without a flatness or regularity assumption.
-/

@[expose] public noncomputable section

namespace Module

universe u v w

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Surjective scalar restriction preserves both principal homology lengths,
including the kernel contribution. -/
theorem principalEuler_of_surjective_algebraMap
    (M : Type w) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (h : Function.Surjective (algebraMap R S)) (c : R) :
    principalEuler (N := M) c = principalEuler (N := M) (algebraMap R S c) := by
  have hk : Module.length R (ScalarKernel M c) =
      Module.length S (ScalarKernel M (algebraMap R S c)) :=
    (scalarKernelRestrictionEquiv (D := S) M c).length_eq.trans
      (Module.length_eq_of_surjective h)
  have hq : Module.length R (ScalarCokernel M c) =
      Module.length S (ScalarCokernel M (algebraMap R S c)) :=
    (scalarCokernelRestrictionEquiv (D := S) M c).length_eq.trans
      (Module.length_eq_of_surjective h)
  exact congrArg₂ (fun q k : ℕ∞ => (q.toNat : ℤ) - (k.toNat : ℤ)) hq hk

/-- The original quotient by the scalar-map kernel retains the exact principal
Euler value on the target ring. -/
theorem principalEuler_quotient_ker_of_surjective
    (h : Function.Surjective (algebraMap R S)) (c : R) :
    principalEuler (N := R ⧸ RingHom.ker (algebraMap R S)) c =
      principalEuler (N := S) (algebraMap R S c) := by
  let e : (R ⧸ RingHom.ker (algebraMap R S)) ≃ₗ[R] S :=
    (Algebra.linearMap R S).quotKerEquivOfSurjective h
  exact (principalEuler_congr e c).trans
    (principalEuler_of_surjective_algebraMap S h c)

/-- An actual principal kernel identifies the original numerator scalar
cokernel with the target ring before the face Euler comparison. -/
theorem principalEuler_scalarCokernel_of_surjective
    (h : Function.Surjective (algebraMap R S)) (n c : R)
    (hker : RingHom.ker (algebraMap R S) = Ideal.span {n}) :
    principalEuler (N := ScalarCokernel R n) c =
      principalEuler (N := S) (algebraMap R S c) := by
  have hr : LinearMap.range (LinearMap.lsmul R R n) =
      (RingHom.ker (algebraMap R S) : Submodule R R) := by
    rw [hker]
    ext x
    change (∃ y : R, n * y = x) ↔ x ∈ Ideal.span {n}
    rw [Ideal.mem_span_singleton]
    exact ⟨fun ⟨y, hy⟩ => ⟨y, hy.symm⟩, fun ⟨y, hy⟩ => ⟨y, hy.symm⟩⟩
  exact (principalEuler_congr (Submodule.quotEquivOfEq _ _ hr) c).trans
    (principalEuler_quotient_ker_of_surjective h c)

end Module
