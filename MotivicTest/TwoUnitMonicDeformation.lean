/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.TwoUnitMonicDeformation
public import Lean.Util.CollectAxioms

/-!
# Consumers of the finite two-unit monic deformation

The tests use the full affine quotient and its entire tensor fibers. An
explicit characteristic-zero example has a nonzero nilpotent in the one
fiber, while the polynomial coordinate is still a genuine unit.
-/

@[expose] public noncomputable section

open Polynomial Polynomial.TwoUnitMonicDeformation

namespace Motivic.MotivicTest.TwoUnitMonicDeformation

universe u

variable {k : Type u} [Field k]

/-- The irreducible-field input yields two actual units in a finite-free family. -/
theorem actual_two_unit_family (p A B : k[X]) (γ : k) (hp : p.Monic)
    (hi : Irreducible p) (hA : A ≠ 0) (hB : B ≠ 0)
    (hdeg : A.natDegree + B.natDegree < p.natDegree) :
    Module.Finite k[X] (AdjoinRoot (family p A B γ)) ∧
      Module.Free k[X] (AdjoinRoot (family p A B γ)) ∧
      Module.FaithfullyFlat k[X] (AdjoinRoot (family p A B γ)) ∧
      IsUnit (coordinate (family p A B γ) A) ∧
      IsUnit (coordinate (family p A B γ) B) := by
  have hfin := finite_free_faithfullyFlat p A B γ hp hdeg
  exact ⟨hfin.1, hfin.2.1, hfin.2.2,
    coordinate_isUnit p A B γ (isCoprime_product hi hA hB hdeg)⟩

/-- Characteristic zero supplies a valid chosen root and strict degree descent
for every irreducible endpoint factor, without removing its multiplicity. -/
theorem characteristic_zero_degree_descent [CharZero k] (p A B : k[X]) (hp : p.Monic)
    (hi : Irreducible p) (hA : A ≠ 0) (hB : B ≠ 0)
    (hdeg : A.natDegree + B.natDegree < p.natDegree) (hn : 1 < p.natDegree) :
    ∃ c : k, A.eval c ≠ 0 ∧ B.eval c ≠ 0 ∧ gamma p A B c ≠ 0 ∧
      (endpointPolynomial p A B (gamma p A B c) 1).eval c = 0 ∧
      ∀ r : k[X], Irreducible r → r ∣ endpointPolynomial p A B (gamma p A B c) 1 →
        r.natDegree < p.natDegree := by
  let : Infinite k := Infinite.of_injective (Nat.cast : ℕ → k) Nat.cast_injective
  obtain ⟨c, hcA, hcB⟩ := exists_good_point A B hA hB
  exact ⟨c, hcA, hcB, gamma_ne_zero p A B c hi hn hcA hcB,
    endpoint_one_eval p A B c hcA hcB,
    fun r hr hd => irreducible_factor_natDegree_lt p A B c hp hdeg hn hcA hcB r hr hd⟩

/-- Both whole endpoint coordinate maps are the specified polynomial images. -/
theorem exact_endpoint_coordinates (p A B : k[X]) (γ s : k)
    (hcop : IsCoprime p (A * B)) :
    TwoUnitPolynomialFamily.endpointFiberEquiv (family p A B γ) s
        (endpointPolynomial p A B γ s) (specialize p A B γ s)
        (Algebra.PolynomialFiber.specialize (AdjoinRoot (family p A B γ)) s
          (firstUnit p A B γ hcop : AdjoinRoot (family p A B γ))) =
      AdjoinRoot.mk (endpointPolynomial p A B γ s) A ∧
    TwoUnitPolynomialFamily.endpointFiberEquiv (family p A B γ) s
        (endpointPolynomial p A B γ s) (specialize p A B γ s)
        (Algebra.PolynomialFiber.specialize (AdjoinRoot (family p A B γ)) s
          (secondUnit p A B γ hcop : AdjoinRoot (family p A B γ))) =
      AdjoinRoot.mk (endpointPolynomial p A B γ s) B := by simp

/-- General equal-degree interpolation can retain both units by a congruence. -/
theorem congruent_endpoints_units (p q A B : k[X]) (hcop : IsCoprime p (A * B))
    (hdiv : A * B ∣ q - p) :
    IsUnit (coordinate (MonicUnitInterpolation.interpolate p q) A) ∧
      IsUnit (coordinate (MonicUnitInterpolation.interpolate p q) B) := by
  have h := interpolate_coordinate_isUnit p q (A * B) hcop hdiv
  simpa only [coordinate, Polynomial.map_mul, map_mul, IsUnit.mul_iff] using h

/-- A concrete characteristic-zero family has a repeated one-endpoint factor. -/
theorem repeated_endpoint :
    endpointPolynomial (X ^ 2 + 1 : ℚ[X]) X 1 2 1 = (X - 1) ^ 2 := by
  simp only [endpointPolynomial, one_mul, mul_one]
  rw [map_ofNat]
  ring

/-- The required coprimality is an explicit Bezout identity. -/
theorem quadratic_coprime : IsCoprime (X ^ 2 + 1 : ℚ[X]) (X * 1) := by
  refine ⟨1, -X, ?_⟩
  ring

/-- The polynomial coordinate is a unit on the full family, before specialization. -/
theorem repeated_family_unit :
    IsUnit (coordinate (family (X ^ 2 + 1 : ℚ[X]) X 1 2) X) :=
  (coordinate_isUnit _ _ _ _ quadratic_coprime).1

/-- The whole repeated-root quotient contains a nonzero nilpotent. -/
theorem repeated_quotient_nonreduced :
    let q := (X - 1 : ℚ[X]) ^ 2
    AdjoinRoot.root q - 1 ≠ 0 ∧ (AdjoinRoot.root q - 1) ^ 2 = 0 := by
  let q := (X - 1 : ℚ[X]) ^ 2
  have hm : q.Monic := (monic_X_sub_C (1 : ℚ)).pow 2
  have hx : AdjoinRoot.root q - 1 = AdjoinRoot.mk q (X - 1) := by simp
  constructor
  · rw [hx]
    apply AdjoinRoot.mk_ne_zero_of_natDegree_lt hm
    · exact (monic_X_sub_C (1 : ℚ)).ne_zero
    · change (X - 1 : ℚ[X]).natDegree < ((X - 1 : ℚ[X]) ^ 2).natDegree
      simp only [natDegree_pow, ← C_1, natDegree_X_sub_C, mul_one]
      decide
  · rw [hx, ← map_pow]
    exact AdjoinRoot.mk_self

/-- The same nonzero nilpotent is present in the actual tensor-product fiber. -/
theorem repeated_tensor_fiber_nonreduced :
    ∃ x : Algebra.PolynomialFiber.Fiber
        (AdjoinRoot (family (X ^ 2 + 1 : ℚ[X]) X 1 2)) (1 : ℚ),
      x ≠ 0 ∧ x ^ 2 = 0 := by
  let e := TwoUnitPolynomialFamily.endpointFiberEquiv
    (family (X ^ 2 + 1 : ℚ[X]) X 1 2) 1 ((X - 1) ^ 2)
    ((specialize _ _ _ _ _).trans repeated_endpoint)
  refine ⟨e.symm (AdjoinRoot.root ((X - 1 : ℚ[X]) ^ 2) - 1), ?_, ?_⟩
  · intro h
    have he : AdjoinRoot.root ((X - 1 : ℚ[X]) ^ 2) - 1 = 0 := by
      simpa using congrArg e h
    exact repeated_quotient_nonreduced.1 he
  · rw [← map_pow, repeated_quotient_nonreduced.2, map_zero]

open Lean in
run_cmd do
  for name in #[``coordinate_isUnit_of_congruent,
      ``isCoprime_of_irreducible_of_natDegree_lt, ``isCoprime_product,
      ``interpolate_coordinate_isUnit, ``family_monic, ``family_natDegree,
      ``specialize, ``endpointPolynomial_zero, ``endpointPolynomial_monic,
      ``endpointPolynomial_natDegree, ``coordinate_isUnit, ``firstUnit, ``secondUnit,
      ``firstUnit_val, ``secondUnit_val, ``finite_free_faithfullyFlat,
      ``endpoint_coordinate, ``endpointFiberEquiv_coordinate, ``exists_good_point,
      ``endpoint_one_eval, ``gamma_ne_zero, ``irreducible_factor_natDegree_lt_of_root,
      ``irreducible_factor_natDegree_lt, ``actual_two_unit_family,
      ``characteristic_zero_degree_descent, ``exact_endpoint_coordinates,
      ``congruent_endpoints_units, ``repeated_endpoint, ``quadratic_coprime,
      ``repeated_family_unit, ``repeated_quotient_nonreduced,
      ``repeated_tensor_fiber_nonreduced] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Finite two-unit deformation, degree descent, and whole nonreduced fiber audit passed."

end Motivic.MotivicTest.TwoUnitMonicDeformation
