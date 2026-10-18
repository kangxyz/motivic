/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Interchange

/-!
# Local signed principal coefficients along a face

The native minimal-prime Euler sums for a numerator and denominator are
compared with their actual scalar actions on the face quotient. The original
module scalars are regular, but neither intermediate quotient is assumed to
be torsion-free. Finite double quotient lengths are retained explicitly.

Adding a multiple of the face equation to a numerator does not change its
Euler expression on the face. In particular, equal numerator and denominator
there cancel with their full kernel and cokernel contributions. These are
local coefficient identities, not a correspondence graph-face theorem.
-/

@[expose] public noncomputable section

universe u v

namespace Module

variable {R : Type u} [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- A multiple of the face equation acts trivially on the actual face
quotient, including when the remaining scalar has torsion. -/
theorem principalEuler_add_face_mul (c a r : R) :
    principalEuler (N := ScalarCokernel M c) (a + c * r) =
      principalEuler (N := ScalarCokernel M c) a := by
  have hc (x : ScalarCokernel M c) : c • x = 0 := by
    obtain ⟨y, rfl⟩ := (LinearMap.range (LinearMap.lsmul R M c)).mkQ_surjective x
    change (LinearMap.range (LinearMap.lsmul R M c)).mkQ (c • y) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨y, rfl⟩
  have he : LinearMap.lsmul R (ScalarCokernel M c) (a + c * r) =
      LinearMap.lsmul R (ScalarCokernel M c) a := by
    apply LinearMap.ext
    intro x
    change (a + c * r) • x = a • x
    rw [add_smul, mul_smul, hc, add_zero]
  unfold principalEuler
  rw [he]

variable [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R M]

/-- The signed native weighted Euler sum specializes by interchanging the
face equation with each original principal equation. All weights are the
actual localized lengths used by `minimalPrimeEulerTerm`. -/
theorem principalEuler_face_difference (c n d : R)
    (hc : IsSMulRegular M c) (hn : IsSMulRegular M n) (hd : IsSMulRegular M d)
    (hcm : c ∈ IsLocalRing.maximalIdeal R)
    (hcn : Module.length R (ScalarCokernel (ScalarCokernel M n) c) ≠ ⊤)
    (hcd : Module.length R (ScalarCokernel (ScalarCokernel M d) c) ≠ ⊤) :
    (∑ p ∈ moduleMinimalPrimes (A := R) (ScalarCokernel M n),
        minimalPrimeEulerTerm (ScalarCokernel M n) c p) -
      (∑ p ∈ moduleMinimalPrimes (A := R) (ScalarCokernel M d),
        minimalPrimeEulerTerm (ScalarCokernel M d) c p) =
      principalEuler (N := ScalarCokernel M c) n -
        principalEuler (N := ScalarCokernel M c) d := by
  rw [← principalEuler_associativity c hcm hcn,
    ← principalEuler_associativity c hcm hcd,
    principalEuler_interchange n c hn hc,
    principalEuler_interchange d c hd hc]

/-- A literal numerator `a + c*r` has the original scalar `a` as its face
coefficient. No regularity on the face quotient is imposed. Taking `a = d`
then gives the zero endpoint of the signed family. -/
theorem principalEuler_face_difference_add_mul (c a d r : R)
    (hc : IsSMulRegular M c) (hn : IsSMulRegular M (a + c * r))
    (hd : IsSMulRegular M d) (hcm : c ∈ IsLocalRing.maximalIdeal R)
    (hcn : Module.length R (ScalarCokernel (ScalarCokernel M (a + c * r)) c) ≠ ⊤)
    (hcd : Module.length R (ScalarCokernel (ScalarCokernel M d) c) ≠ ⊤) :
    (∑ p ∈ moduleMinimalPrimes (A := R) (ScalarCokernel M (a + c * r)),
        minimalPrimeEulerTerm (ScalarCokernel M (a + c * r)) c p) -
      (∑ p ∈ moduleMinimalPrimes (A := R) (ScalarCokernel M d),
        minimalPrimeEulerTerm (ScalarCokernel M d) c p) =
      principalEuler (N := ScalarCokernel M c) a -
        principalEuler (N := ScalarCokernel M c) d := by
  rw [principalEuler_face_difference M c (a + c * r) d hc hn hd hcm hcn hcd,
    principalEuler_add_face_mul]

/-- The zero face cancels the actual numerator and denominator contributions,
not their individual lengths or their individual support points. -/
theorem principalEuler_face_difference_eq_zero (c d r : R)
    (hc : IsSMulRegular M c) (hn : IsSMulRegular M (d + c * r))
    (hd : IsSMulRegular M d) (hcm : c ∈ IsLocalRing.maximalIdeal R)
    (hcn : Module.length R (ScalarCokernel (ScalarCokernel M (d + c * r)) c) ≠ ⊤)
    (hcd : Module.length R (ScalarCokernel (ScalarCokernel M d) c) ≠ ⊤) :
    (∑ p ∈ moduleMinimalPrimes (A := R) (ScalarCokernel M (d + c * r)),
        minimalPrimeEulerTerm (ScalarCokernel M (d + c * r)) c p) -
      (∑ p ∈ moduleMinimalPrimes (A := R) (ScalarCokernel M d),
        minimalPrimeEulerTerm (ScalarCokernel M d) c p) = 0 := by
  rw [principalEuler_face_difference_add_mul M c d d r hc hn hd hcm hcn hcd,
    sub_self]

end Module
