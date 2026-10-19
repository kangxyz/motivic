/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.PolynomialAlgebra
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Polynomial.Monic

/-!
# Regular graph coordinates and boundary normalization

The boundary ring need not be reduced. A graph coordinate is monic before
flat base change, and regular cancellation determines the boundary value of
the unit relating two generators without ever inverting that coordinate.


Intended upstream module: `Aglib.RingTheory.TensorProduct.RegularGraphBoundary`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.MarkedGraphCoordinateRegular`.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Ideal

/-- Equal principal ideals on an integral target give a unit multiplier whose
boundary value is one whenever the common boundary coordinate is regular. -/
theorem exists_unit_mul_and_map_eq_one_of_span_eq
    {R Q : Type*} [CommRing R] [IsDomain R] [CommRing Q]
    (ρ : R →+* Q) {n c : R}
    (h : Ideal.span ({n} : Set R) = Ideal.span ({c} : Set R))
    (hc : IsSMulRegular Q (ρ c)) (hρ : ρ n = ρ c) :
    ∃ u : Rˣ, n = (u : R) * c ∧ ρ (u : R) = 1 := by
  obtain ⟨u, hu⟩ := (Ideal.span_singleton_eq_span_singleton.mp h).symm
  have hn : n = (u : R) * c := by simpa only [mul_comm] using hu.symm
  refine ⟨u, hn, ?_⟩
  apply hc
  change ρ c * ρ (u : R) = ρ c * 1
  rw [mul_one, mul_comm, ← map_mul, ← hn, hρ]

end Ideal

namespace Algebra.TensorProduct

/-- The actual graph equation on the coefficient-base-changed affine line
is regular even over a nonreduced coefficient algebra. -/
theorem isSMulRegular_graphCoordinate {A Q : Type*} [CommRing A] [CommRing Q]
    [Algebra A Q] (z : Q) :
    IsSMulRegular (Polynomial A ⊗[A] Q)
      ((Polynomial.X : Polynomial A) ⊗ₜ[A] (1 : Q) - (1 : Polynomial A) ⊗ₜ[A] z) := by
  let e : Polynomial Q ≃ₐ[A] Polynomial A ⊗[A] Q :=
    (polyEquivTensor A Q).trans (Algebra.TensorProduct.comm A Q (Polynomial A))
  let c : Polynomial A ⊗[A] Q :=
    (Polynomial.X : Polynomial A) ⊗ₜ[A] (1 : Q) - (1 : Polynomial A) ⊗ₜ[A] z
  have he : e (Polynomial.X - Polynomial.C z) = c := by
    simp [e, c, polyEquivTensor_apply]
  have hc : e.symm c = Polynomial.X - Polynomial.C z := by
    rw [← he, AlgEquiv.symm_apply_apply]
  intro x y h
  apply e.symm.injective
  apply (Polynomial.monic_X_sub_C z).isRegular.left
  change c * x = c * y at h
  have hh := congrArg e.symm h
  simpa only [map_mul, hc] using hh

/-- The original graph coordinate stays regular on any flat algebra over
its literal tensor-product coordinate ring. No reducedness is required. -/
theorem isSMulRegular_graphCoordinate_of_flat
    {A Q S : Type*} [CommRing A] [CommRing Q] [CommRing S] [Algebra A Q]
    [Algebra (Polynomial A ⊗[A] Q) S] [Module.Flat (Polynomial A ⊗[A] Q) S]
    (z : Q) :
    IsSMulRegular S (algebraMap (Polynomial A ⊗[A] Q) S
      ((Polynomial.X : Polynomial A) ⊗ₜ[A] (1 : Q) - (1 : Polynomial A) ⊗ₜ[A] z)) :=
  (isSMulRegular_graphCoordinate z).of_flat

end Algebra.TensorProduct
