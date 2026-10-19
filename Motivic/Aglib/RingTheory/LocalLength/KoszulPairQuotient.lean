/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.LocalLength.KoszulPair

/-!
# The actual quotient by two local equations

Zeroth Koszul homology is identified with the iterated quotient by the two
scalars. This is an explicit linear equivalence of the quotient modules, which
allows the principal local-length formula to act on two-equation intersections.
It imposes no regularity assumption; higher Koszul homology remains separate.
-/

@[expose] public section

universe u v

namespace Module.KoszulPair

variable {R : Type u} [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M] (a b : R)

/-- The boundary submodule in degree zero is exactly `aM + bM`. -/
theorem range_d₁ : LinearMap.range (d₁ M a b) =
    LinearMap.range (LinearMap.lsmul R M a) ⊔
      LinearMap.range (LinearMap.lsmul R M b) :=
  LinearMap.range_coprod _ _

/-- Scalar multiplication in the first quotient has the expected image. -/
theorem range_scalar_quotient :
    LinearMap.range (LinearMap.lsmul R (PrincipalQuotient M a) b) =
      (LinearMap.range (LinearMap.lsmul R M b)).map
        (LinearMap.range (LinearMap.lsmul R M a)).mkQ := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := (LinearMap.range (LinearMap.lsmul R M a)).mkQ_surjective y
    exact ⟨b • z, ⟨z, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    exact ⟨Submodule.Quotient.mk z, rfl⟩

/-- Taking two principal quotients gives the actual zeroth Koszul homology. -/
noncomputable def iteratedQuotientEquiv :
    PrincipalQuotient (PrincipalQuotient M a) b ≃ₗ[R] H₀ M a b :=
  (Submodule.quotEquivOfEq _ _ (range_scalar_quotient M a b)).trans
    ((Submodule.quotientQuotientEquivQuotientSup
      (LinearMap.range (LinearMap.lsmul R M a))
      (LinearMap.range (LinearMap.lsmul R M b))).trans
        (Submodule.quotEquivOfEq _ _ (range_d₁ M a b).symm))

end Module.KoszulPair
