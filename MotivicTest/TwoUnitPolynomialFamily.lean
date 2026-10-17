/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.TwoUnitPolynomialFamily
public import Mathlib.Algebra.Field.ZMod

/-!
# Consumers of two-unit polynomial families

These tests use the original quotient and whole tensor fibers. They check
both coordinates and scalar values, including an admissible characteristic-
three cubic with a nonzero nilpotent. No Steinberg relation is asserted.
-/

@[expose] public section

noncomputable section

open Polynomial Polynomial.TwoUnitPolynomialFamily
open Algebra.PolynomialFiber

namespace Motivic.MotivicTest.TwoUnitPolynomialFamily

universe u

variable {k : Type u} [Field k]

/-- Generic monic positive-degree families retain both actual units. -/
theorem two_unit_package (f : k[X][X]) (hf : f.Monic) (hd : 0 < f.natDegree)
    (h0 : IsUnit (f.eval 0)) (h1 : IsUnit (f.eval 1)) :
    Module.Finite k[X] (AdjoinRoot f) ∧ Module.Free k[X] (AdjoinRoot f) ∧
      FaithfulSMul k[X] (AdjoinRoot f) ∧ Module.FaithfullyFlat k[X] (AdjoinRoot f) ∧
      IsUnit (AdjoinRoot.root f) ∧ IsUnit (1 - AdjoinRoot.root f) :=
  ⟨(finite_free hf).1, (finite_free hf).2, faithfulSMul hf hd, faithfullyFlat hf hd,
    by simpa using (rootUnit f h0).isUnit,
    by simpa using (oneSubRootUnit f h1).isUnit⟩

/-- The two named units specialize to the prescribed two coordinates. -/
theorem endpoint_units (f : k[X][X]) (s : k) (p : k[X])
    (hp : f.map (evalRingHom s) = p) (h0 : IsUnit (f.eval 0))
    (h1 : IsUnit (f.eval 1)) :
    endpoint f s p hp (rootUnit f h0 : AdjoinRoot f) = AdjoinRoot.root p ∧
      endpoint f s p hp (oneSubRootUnit f h1 : AdjoinRoot f) = 1 - AdjoinRoot.root p := by
  simp

/-- Whole tensor fibers preserve both actual unit values and the parameter. -/
theorem tensor_endpoint_units_and_parameter (f : k[X][X]) (s : k) (p : k[X])
    (hp : f.map (evalRingHom s) = p) (h0 : IsUnit (f.eval 0))
    (h1 : IsUnit (f.eval 1)) :
    endpointFiberEquiv f s p hp (specialize (AdjoinRoot f) s
      (rootUnit f h0 : AdjoinRoot f)) = AdjoinRoot.root p ∧
    endpointFiberEquiv f s p hp (specialize (AdjoinRoot f) s
      (oneSubRootUnit f h1 : AdjoinRoot f)) = 1 - AdjoinRoot.root p ∧
    endpointFiberEquiv f s p hp (specialize (AdjoinRoot f) s
      (AdjoinRoot.of f X)) = AdjoinRoot.of p s := by simp

/-- Existing determinant-norm invariance applies separately to both units. -/
theorem both_coordinate_fiber_norms (f : k[X][X]) (hf : f.Monic)
    (h0 : IsUnit (f.eval 0)) (h1 : IsUnit (f.eval 1)) (s t : k) :
    Algebra.norm k (specialize (AdjoinRoot f) s (AdjoinRoot.root f)) =
        Algebra.norm k (specialize (AdjoinRoot f) t (AdjoinRoot.root f)) ∧
      Algebra.norm k (specialize (AdjoinRoot f) s (1 - AdjoinRoot.root f)) =
        Algebra.norm k (specialize (AdjoinRoot f) t (1 - AdjoinRoot.root f)) := by
  let : Module.Free k[X] (AdjoinRoot f) := hf.free_adjoinRoot
  let : Module.Finite k[X] (AdjoinRoot f) := hf.finite_adjoinRoot
  exact ⟨by simpa using norm_specialize_eq (rootUnit f h0) s t,
    by simpa using norm_specialize_eq (oneSubRootUnit f h1) s t⟩

/-- The literal outer evaluations distinguish admissibility from parameter
specialization; both hypotheses are necessary for the respective unit values. -/
theorem cubic_outer_values (a : k) :
    (cubic a).eval 0 = C (-(a ^ 3)) ∧ (cubic a).eval 1 = C (1 - a ^ 3) ∧
      (IsUnit ((cubic a).eval 0) ↔ a ≠ 0) ∧
      (IsUnit ((cubic a).eval 1) ↔ a ^ 3 ≠ 1) :=
  ⟨cubic_eval_zero a, cubic_eval_one a,
    cubic_eval_zero_isUnit_iff a, cubic_eval_one_isUnit_iff a⟩

/-- Both complete endpoint polynomials, without selecting reduced factors. -/
theorem cubic_parameter_endpoints (a : k) :
    (cubic a).map (evalRingHom 0) = X ^ 3 - C (a ^ 3) ∧
      (cubic a).map (evalRingHom 1) = (X - C (a ^ 3)) * (X ^ 2 - X + 1) :=
  ⟨cubic_specialize_zero a, cubic_specialize_one a⟩

/-- Scalar quotient maps send the parameter to the actual endpoint scalar. -/
theorem cubic_scalar_coordinates (a : k) :
    cubicEndpointZero a (AdjoinRoot.of (cubic a) X) = 0 ∧
      cubicEndpointOne a (AdjoinRoot.of (cubic a) X) = 1 ∧
      cubicEndpointZero a (AdjoinRoot.root (cubic a)) = AdjoinRoot.root (cubicZero a) ∧
      cubicEndpointOne a (1 - AdjoinRoot.root (cubic a)) =
        1 - AdjoinRoot.root (cubicOne a) := by simp

/-- Both whole tensor fibers retain the parameter scalar and both coordinates. -/
theorem cubic_tensor_coordinates (a : k) :
    cubicFiberZeroEquiv a (specialize (AdjoinRoot (cubic a)) 0
      (AdjoinRoot.of (cubic a) X)) = 0 ∧
    cubicFiberOneEquiv a (specialize (AdjoinRoot (cubic a)) 1
      (AdjoinRoot.of (cubic a) X)) = 1 ∧
    cubicFiberZeroEquiv a (specialize (AdjoinRoot (cubic a)) 0
      (AdjoinRoot.root (cubic a))) = AdjoinRoot.root (cubicZero a) ∧
    cubicFiberZeroEquiv a (specialize (AdjoinRoot (cubic a)) 0
      (1 - AdjoinRoot.root (cubic a))) = 1 - AdjoinRoot.root (cubicZero a) ∧
    cubicFiberOneEquiv a (specialize (AdjoinRoot (cubic a)) 1
      (AdjoinRoot.root (cubic a))) = AdjoinRoot.root (cubicOne a) ∧
    cubicFiberOneEquiv a (specialize (AdjoinRoot (cubic a)) 1
      (1 - AdjoinRoot.root (cubic a))) = 1 - AdjoinRoot.root (cubicOne a) := by simp

/-- The excluded integral-graph condition may fail in an admissible cubic. -/
theorem characteristic_three_admissible :
    (-1 : ZMod 3) ^ 3 + 1 = 0 ∧
      Module.FaithfullyFlat (ZMod 3)[X] (AdjoinRoot (cubic (-1 : ZMod 3))) ∧
      IsUnit (AdjoinRoot.root (cubic (-1 : ZMod 3))) ∧
      IsUnit (1 - AdjoinRoot.root (cubic (-1 : ZMod 3))) := by
  have h := cubic_admissible (-1 : ZMod 3) (by decide) (by decide)
  exact ⟨by decide, h.2.2.2⟩

/-- In characteristic three the whole zero fiber has a triple root. -/
theorem characteristic_three_zero_polynomial :
    cubicZero (-1 : ZMod 3) = (X + 1) ^ 3 := by
  unfold cubicZero
  have h3 : (3 : (ZMod 3)[X]) = 0 := CharP.cast_eq_zero (ZMod 3)[X] 3
  have ha : (-1 : ZMod 3) ^ 3 = -1 := by decide
  rw [ha]
  simp only [map_neg, map_one, sub_neg_eq_add]
  calc
    X ^ 3 + 1 = (X + 1) ^ 3 - 3 * X ^ 2 - 3 * X := by ring
    _ = (X + 1) ^ 3 := by rw [h3]; ring

/-- A nonzero nilpotent in the literal cubic quotient; no reduction occurs. -/
theorem characteristic_three_zero_quotient_nonreduced :
    let p := cubicZero (-1 : ZMod 3)
    AdjoinRoot.root p + 1 ≠ 0 ∧ (AdjoinRoot.root p + 1) ^ 3 = 0 := by
  let p := cubicZero (-1 : ZMod 3)
  have hp : p.Monic := monic_X_pow_sub_C _ (by decide)
  have hd : p.natDegree = 3 := natDegree_X_pow_sub_C
  have hmk : AdjoinRoot.root p + 1 = AdjoinRoot.mk p (X + 1) := by simp
  constructor
  · rw [hmk]
    apply AdjoinRoot.mk_ne_zero_of_natDegree_lt hp
    · exact (monic_X_add_C (1 : ZMod 3)).ne_zero
    · rw [hd]
      compute_degree
      norm_num
  · rw [hmk, ← map_pow, ← characteristic_three_zero_polynomial]
    exact AdjoinRoot.mk_self

/-- The nonzero nilpotent survives in the actual tensor-product zero fiber. -/
theorem characteristic_three_zero_tensor_nonreduced :
    ∃ x : Fiber (AdjoinRoot (cubic (-1 : ZMod 3))) (0 : ZMod 3),
      x ≠ 0 ∧ x ^ 3 = 0 := by
  let e := cubicFiberZeroEquiv (-1 : ZMod 3)
  refine ⟨e.symm (AdjoinRoot.root (cubicZero (-1 : ZMod 3)) + 1), ?_, ?_⟩
  · intro h
    have : AdjoinRoot.root (cubicZero (-1 : ZMod 3)) + 1 = 0 := by
      simpa using congrArg e h
    exact characteristic_three_zero_quotient_nonreduced.1 this
  · rw [← map_pow, characteristic_three_zero_quotient_nonreduced.2, map_zero]

open Lean in
run_cmd do
  for name in #[``AdjoinRoot.isUnit_of_sub_root_of_isUnit_eval,
      ``AdjoinRoot.isUnit_one_sub_root_of_isUnit_eval_one, ``finite_free,
      ``Polynomial.TwoUnitPolynomialFamily.faithfulSMul, ``faithfullyFlat,
      ``rootUnit, ``oneSubRootUnit,
      ``rootUnit_val, ``oneSubRootUnit_val, ``endpoint, ``endpoint_root,
      ``endpoint_one_sub_root, ``endpoint_of, ``endpointFiberEquiv,
      ``endpointFiberEquiv_root, ``endpointFiberEquiv_one_sub_root,
      ``endpointFiberEquiv_of, ``cubic, ``cubicZero, ``cubicOne,
      ``cubic_monic, ``cubic_natDegree, ``cubic_eval_zero, ``cubic_eval_one,
      ``cubic_eval_zero_isUnit_iff, ``cubic_eval_one_isUnit_iff,
      ``cubic_eval_zero_isUnit, ``cubic_eval_one_isUnit, ``cubic_specialize_zero,
      ``cubic_specialize_one, ``cubicPowerBasis, ``cubicPowerBasis_dim,
      ``cubic_admissible, ``cubicEndpointZero, ``cubicEndpointOne,
      ``cubicFiberZeroEquiv, ``cubicFiberOneEquiv, ``cubicEndpointZero_root,
      ``cubicEndpointOne_root, ``cubicFiberZeroEquiv_root, ``cubicFiberOneEquiv_root,
      ``cubicEndpointZero_one_sub_root, ``cubicEndpointOne_one_sub_root,
      ``cubicEndpointZero_of, ``cubicEndpointOne_of,
      ``cubicFiberZeroEquiv_one_sub_root, ``cubicFiberOneEquiv_one_sub_root,
      ``cubicFiberZeroEquiv_of, ``cubicFiberOneEquiv_of, ``two_unit_package,
      ``endpoint_units, ``tensor_endpoint_units_and_parameter,
      ``both_coordinate_fiber_norms, ``cubic_outer_values, ``cubic_parameter_endpoints,
      ``cubic_scalar_coordinates, ``cubic_tensor_coordinates,
      ``characteristic_three_admissible, ``characteristic_three_zero_polynomial,
      ``characteristic_three_zero_quotient_nonreduced,
      ``characteristic_three_zero_tensor_nonreduced] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Two-unit family and nonreduced cubic fiber audit passed: standard foundations only."

end Motivic.MotivicTest.TwoUnitPolynomialFamily
