/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.MonicUnitInterpolation
public import Mathlib.Algebra.Field.ZMod

/-!
# Consumers of the literal monic unit interpolation

These tests use the actual quotient algebra and its whole tensor-product
fibers. The repeated-root example supplies a nonzero nilpotent over every
field, including characteristic two. No cycle or motivic comparison is
asserted here.
-/

@[expose] public section

noncomputable section

open Polynomial Polynomial.MonicUnitInterpolation
open Algebra.PolynomialFiber

namespace Motivic.MotivicTest.MonicUnitInterpolation

universe u

variable {k : Type u} [Field k]

/-- Positive-degree monic input produces a finite free quotient of the
same rank, and the Laurent coordinate is an actual unit. -/
theorem family_package (p : k[X]) (hp : p.Monic) (hd : 1 ≤ p.natDegree)
    (h0 : p.coeff 0 ≠ 0) :
    (family p).Monic ∧ (family p).natDegree = p.natDegree ∧
      (family p).coeff 0 = C (p.coeff 0) ∧
      Module.Free k[X] (FamilyAlgebra p) ∧
      Module.Finite k[X] (FamilyAlgebra p) ∧
      IsUnit (AdjoinRoot.root (family p)) :=
  ⟨family_monic hp hd, family_natDegree hp hd, family_coeff_zero p hd,
    family_free hp hd, family_finite hp hd,
    adjoinRoot_root_isUnit _ (family_coeff_zero_isUnit p hd h0)⟩

/-- The exported basis has exactly the intended number of vectors. -/
theorem family_basis_size (p : k[X]) (hp : p.Monic) (hd : 1 ≤ p.natDegree) :
    (familyPowerBasis hp hd).dim = p.natDegree := familyPowerBasis_dim hp hd

/-- Both specialized unit values are the literal adjoined coordinates. -/
theorem coordinate_endpoints (p : k[X]) (hd : 1 ≤ p.natDegree)
    (h0 : p.coeff 0 ≠ 0) :
    endpointZero p (coordinateUnit p hd h0 : FamilyAlgebra p) = AdjoinRoot.root p ∧
      endpointOne p (coordinateUnit p hd h0 : FamilyAlgebra p) =
        AdjoinRoot.root (target p) := by simp

/-- The actual norm-invariance theorem applies to this finite free family. -/
theorem family_fiber_norm_eq (p : k[X]) (hp : p.Monic) (hd : 1 ≤ p.natDegree)
    (h0 : p.coeff 0 ≠ 0) :
    Algebra.norm k (specialize (FamilyAlgebra p) (0 : k) (AdjoinRoot.root (family p))) =
      Algebra.norm k (specialize (FamilyAlgebra p) (1 : k)
        (AdjoinRoot.root (family p))) := by
  let : Module.Free k[X] (FamilyAlgebra p) := family_free hp hd
  let : Module.Finite k[X] (FamilyAlgebra p) := family_finite hp hd
  simpa using norm_specialize_eq (coordinateUnit p hd h0) (0 : k) (1 : k)

/-- The degree-two family has exactly the multiplicative endpoint needed
for a later cycle-level unit relation. -/
theorem target_pair (a b : k) :
    target ((X - C a) * (X - C b)) = (X - C 1) * (X - C (a * b)) := by
  have hd : ((X - C a) * (X - C b)).natDegree = 2 := by
    rw [(monic_X_sub_C a).natDegree_mul (monic_X_sub_C b),
      natDegree_X_sub_C, natDegree_X_sub_C]
  rw [target, normValue, hd]
  simp [coeff_zero_eq_eval_zero]

/-- A double identity root remains a double root at the split endpoint. -/
theorem target_double_identity :
    target ((X - C (1 : k)) ^ 2) = (X - C 1) ^ 2 := by
  have hd : ((X - C (1 : k)) ^ 2).natDegree = 2 := by
    rw [natDegree_pow, natDegree_X_sub_C, mul_one]
  rw [target, normValue, hd]
  simp [coeff_zero_eq_eval_zero, pow_two]

/-- The actual quotient by `(T - 1)^2` has a nonzero square-zero element,
without a restriction on the characteristic. -/
theorem double_identity_nonreduced :
    let f : k[X] := (X - C 1) ^ 2
    AdjoinRoot.root f - 1 ≠ 0 ∧ (AdjoinRoot.root f - 1) ^ 2 = 0 := by
  let f : k[X] := (X - C 1) ^ 2
  have hmk : AdjoinRoot.root f - 1 = AdjoinRoot.mk f (X - C 1) := by
    simp only [map_sub, map_one, AdjoinRoot.mk_X]
  constructor
  · rw [hmk]
    apply AdjoinRoot.mk_ne_zero_of_natDegree_lt ((monic_X_sub_C (1 : k)).pow 2)
      (X_sub_C_ne_zero _)
    change (X - C (1 : k)).natDegree < ((X - C (1 : k)) ^ 2).natDegree
    rw [natDegree_pow, natDegree_X_sub_C]
    decide
  · rw [hmk, ← map_pow, AdjoinRoot.mk_self]

/-- This nonzero nilpotent survives in the actual tensor fiber of the
constructed family, rather than only in an auxiliary presentation. -/
theorem double_identity_zero_fiber_nonreduced :
    let p : k[X] := (X - C 1) ^ 2
    ∃ x : Fiber (FamilyAlgebra p) (0 : k), x ≠ 0 ∧ x ^ 2 = 0 := by
  let p : k[X] := (X - C 1) ^ 2
  let e := fiberZeroEquiv p
  refine ⟨e.symm (AdjoinRoot.root p - 1), ?_, ?_⟩
  · intro h
    have : AdjoinRoot.root p - 1 = 0 := by
      simpa using congrArg e h
    exact (double_identity_nonreduced (k := k)).1 this
  · rw [← map_pow, (double_identity_nonreduced (k := k)).2, map_zero]

/-- A concrete positive-characteristic consumer of the whole-fiber theorem. -/
theorem characteristic_two_nonreduced :
    let p : (ZMod 2)[X] := (X - C 1) ^ 2
    ∃ x : Fiber (FamilyAlgebra p) (0 : ZMod 2), x ≠ 0 ∧ x ^ 2 = 0 :=
  double_identity_zero_fiber_nonreduced

open Lean in
run_cmd do
  for name in #[``normValue_ne_zero, ``target_monic, ``target_natDegree,
      ``target_coeff_zero, ``interpolate_coeff, ``interpolate_monic_natDegree,
      ``interpolate_coeff_zero, ``interpolate_specialize,
      ``interpolate_specialize_zero, ``interpolate_specialize_one,
      ``family_monic_natDegree, ``family_monic, ``family_natDegree,
      ``family_coeff_zero, ``family_coeff_zero_isUnit,
      ``family_specialize_zero, ``family_specialize_one,
      ``familyPowerBasis, ``familyPowerBasis_dim, ``family_free, ``family_finite,
      ``adjoinRoot_root_isUnit, ``coordinateUnit, ``coordinateUnit_val,
      ``endpointZero, ``endpointOne, ``endpointZero_root, ``endpointOne_root,
      ``endpointZero_of, ``endpointOne_of, ``fiberEquiv, ``fiberEquiv_root,
      ``fiberZeroEquiv, ``fiberOneEquiv, ``fiberZeroEquiv_root, ``fiberOneEquiv_root,
      ``family_package, ``family_basis_size, ``coordinate_endpoints,
      ``family_fiber_norm_eq, ``target_pair, ``target_double_identity,
      ``double_identity_nonreduced, ``double_identity_zero_fiber_nonreduced,
      ``characteristic_two_nonreduced] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Monic unit interpolation and nonreduced-fiber audit passed: standard foundations only."

end Motivic.MotivicTest.MonicUnitInterpolation
