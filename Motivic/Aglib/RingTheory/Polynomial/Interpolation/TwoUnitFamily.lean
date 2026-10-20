/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Polynomial.Interpolation.MonicUnit
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.Tactic.ComputeDegree

/-!
# Literal polynomial families with two invertible coordinates

A monic polynomial of positive degree over `k[t]` defines a finite free,
faithfully flat quotient. Unit evaluations at outer-variable zero and one
make both the adjoined root and its complement units. Scalar specialization
and the existing whole tensor-fiber equivalence preserve both coordinates.

The cubic `X³ - t(a³+1)X² + t(a³+1)X - a³` is admissible when `a ≠ 0`
and `a³ ≠ 1`. No assumption on `a³+1`, characteristic, reducedness, or
separability is used. These are algebraic prerequisites only: no motivic
relation or correspondence is asserted here.
-/

@[expose] public section

noncomputable section

open Polynomial
open scoped TensorProduct

namespace AdjoinRoot

/-- A unit evaluation makes the difference from the adjoined root a unit.
This applies to the full quotient over an arbitrary commutative ring. -/
lemma isUnit_of_sub_root_of_isUnit_eval {R : Type*} [CommRing R]
    (f : R[X]) (r : R) (hr : IsUnit (f.eval r)) :
    IsUnit (of f r - root f) := by
  obtain ⟨q, hq⟩ := X_sub_C_dvd_sub_C_eval (p := f) (a := r)
  have hrel : (of f r - root f) * mk f q = of f (f.eval r) := by
    have h := congrArg (mk f) hq
    simp only [map_sub, map_mul, mk_self, mk_X, mk_C, zero_sub] at h
    linear_combination h
  have hu : IsUnit ((of f r - root f) * mk f q) := by
    rw [hrel]
    exact hr.map (of f)
  exact (IsUnit.mul_iff.mp hu).1

/-- Unit value at one gives the second torus coordinate `1 - root`. -/
lemma isUnit_one_sub_root_of_isUnit_eval_one {R : Type*} [CommRing R]
    (f : R[X]) (h1 : IsUnit (f.eval 1)) : IsUnit (1 - root f) := by
  simpa using isUnit_of_sub_root_of_isUnit_eval f 1 h1

end AdjoinRoot

namespace Polynomial.TwoUnitPolynomialFamily

universe u

variable {k : Type u} [Field k]

/-- The original quotient is finite free; nilpotents are retained. -/
lemma finite_free {f : k[X][X]} (hf : f.Monic) :
    Module.Finite k[X] (AdjoinRoot f) ∧ Module.Free k[X] (AdjoinRoot f) :=
  ⟨hf.finite_adjoinRoot, hf.free_adjoinRoot⟩

/-- Positive degree makes the scalar action faithful. -/
lemma faithfulSMul {f : k[X][X]} (hf : f.Monic) (hd : 0 < f.natDegree) :
    FaithfulSMul k[X] (AdjoinRoot f) :=
  AdjoinRoot.faithfulSMul_of_monic_of_degree_pos hf (natDegree_pos_iff_degree_pos.mp hd)

/-- The actual quotient is faithfully flat over the parameter line. -/
lemma faithfullyFlat {f : k[X][X]} (hf : f.Monic) (hd : 0 < f.natDegree) :
    Module.FaithfullyFlat k[X] (AdjoinRoot f) := by
  let : Module.Free k[X] (AdjoinRoot f) := hf.free_adjoinRoot
  let : Nontrivial (AdjoinRoot f) :=
    (AdjoinRoot.nontrivial_iff_of_monic hf).mpr (natDegree_pos_iff_degree_pos.mp hd)
  infer_instance

/-- The first coordinate as an actual unit of the quotient. -/
def rootUnit {R : Type u} [CommRing R] (f : R[X]) (h0 : IsUnit (f.eval 0)) : (AdjoinRoot f)ˣ :=
  (MonicUnitInterpolation.adjoinRoot_root_isUnit f
    (by simpa only [coeff_zero_eq_eval_zero] using h0)).unit

/-- The complementary coordinate as an actual unit of the quotient. -/
def oneSubRootUnit {R : Type u} [CommRing R] (f : R[X]) (h1 : IsUnit (f.eval 1)) :
    (AdjoinRoot f)ˣ :=
  (AdjoinRoot.isUnit_one_sub_root_of_isUnit_eval_one f h1).unit

@[simp] lemma rootUnit_val {R : Type u} [CommRing R] (f : R[X]) (h0 : IsUnit (f.eval 0)) :
    (rootUnit f h0 : AdjoinRoot f) = AdjoinRoot.root f := IsUnit.unit_spec _

@[simp] lemma oneSubRootUnit_val {R : Type u} [CommRing R] (f : R[X]) (h1 : IsUnit (f.eval 1)) :
    (oneSubRootUnit f h1 : AdjoinRoot f) = 1 - AdjoinRoot.root f := IsUnit.unit_spec _

/-- The actual scalar-specialization map to a chosen presentation of a fiber. -/
def endpoint (f : k[X][X]) (s : k) (p : k[X])
    (hp : f.map (evalRingHom s) = p) : AdjoinRoot f →+* AdjoinRoot p :=
  AdjoinRoot.map (evalRingHom s) f p (by rw [hp])

@[simp] lemma endpoint_root (f : k[X][X]) (s : k) (p : k[X])
    (hp : f.map (evalRingHom s) = p) :
    endpoint f s p hp (AdjoinRoot.root f) = AdjoinRoot.root p :=
  AdjoinRoot.map_root _ _ _ _

@[simp] lemma endpoint_one_sub_root (f : k[X][X]) (s : k) (p : k[X])
    (hp : f.map (evalRingHom s) = p) :
    endpoint f s p hp (1 - AdjoinRoot.root f) = 1 - AdjoinRoot.root p := by simp

@[simp] lemma endpoint_of (f : k[X][X]) (s : k) (p : k[X])
    (hp : f.map (evalRingHom s) = p) (r : k[X]) :
    endpoint f s p hp (AdjoinRoot.of f r) = AdjoinRoot.of p (r.eval s) :=
  AdjoinRoot.map_of _ _ _ _ _

/-- Reuse the whole tensor-fiber equivalence, then change only its polynomial
presentation. This is not a passage to a reduction or to selected factors. -/
def endpointFiberEquiv (f : k[X][X]) (s : k) (p : k[X])
    (hp : f.map (evalRingHom s) = p) :
    Algebra.PolynomialFiber.Fiber (AdjoinRoot f) s ≃ₐ[k] AdjoinRoot p :=
  (MonicUnitInterpolation.fiberEquiv f s).trans (AdjoinRoot.algEquivOfEq k _ _ hp)

@[simp] lemma endpointFiberEquiv_root (f : k[X][X]) (s : k) (p : k[X])
    (hp : f.map (evalRingHom s) = p) :
    endpointFiberEquiv f s p hp (Algebra.PolynomialFiber.specialize (AdjoinRoot f) s
      (AdjoinRoot.root f)) = AdjoinRoot.root p := by
  simp [endpointFiberEquiv, AdjoinRoot.algEquivOfEq_root]

lemma endpointFiberEquiv_one_sub_root (f : k[X][X]) (s : k) (p : k[X])
    (hp : f.map (evalRingHom s) = p) :
    endpointFiberEquiv f s p hp (Algebra.PolynomialFiber.specialize (AdjoinRoot f) s
      (1 - AdjoinRoot.root f)) = 1 - AdjoinRoot.root p := by simp

@[simp] lemma endpointFiberEquiv_of (f : k[X][X]) (s : k) (p : k[X])
    (hp : f.map (evalRingHom s) = p) (r : k[X]) :
    endpointFiberEquiv f s p hp (Algebra.PolynomialFiber.specialize (AdjoinRoot f) s
      (AdjoinRoot.of f r)) = AdjoinRoot.of p (r.eval s) := by
  have h : MonicUnitInterpolation.fiberEquiv f s
      (Algebra.PolynomialFiber.specialize (AdjoinRoot f) s (AdjoinRoot.of f r)) =
      AdjoinRoot.of (f.map (evalRingHom s)) (r.eval s) := by
    let := Algebra.PolynomialFiber.evaluationAlgebra s
    change MonicUnitInterpolation.fiberEquiv f s (1 ⊗ₜ[k[X]] AdjoinRoot.of f r) = _
    dsimp only [MonicUnitInterpolation.fiberEquiv]
    rw [AlgEquiv.trans_apply, AdjoinRoot.tensorAlgEquiv_of,
      AdjoinRoot.coe_mapAlgEquiv, AdjoinRoot.map_of]
    change AdjoinRoot.of _ ((Algebra.TensorProduct.rid k[X] k k)
      (1 ⊗ₜ[k[X]] r)) = _
    rw [Algebra.TensorProduct.rid_tmul, Algebra.smul_def, mul_one]
    rfl
  change AdjoinRoot.algEquivOfEq k _ _ hp
    (MonicUnitInterpolation.fiberEquiv f s _) = _
  rw [h]
  exact (AdjoinRoot.algEquivOfEq k _ _ hp).commutes _

/-- The explicit cubic, with the parameter in the coefficient ring. -/
def cubic (a : k) : k[X][X] :=
  X ^ 3 - C (X * C (a ^ 3 + 1)) * X ^ 2 + C (X * C (a ^ 3 + 1)) * X - C (C (a ^ 3))

/-- The full zero-endpoint polynomial, without choosing its roots. -/
def cubicZero (a : k) : k[X] := X ^ 3 - C (a ^ 3)

/-- The full one-endpoint polynomial, retaining both factors and multiplicities. -/
def cubicOne (a : k) : k[X] := (X - C (a ^ 3)) * (X ^ 2 - X + 1)

lemma cubic_monic (a : k) : (cubic a).Monic := by
  unfold cubic
  monicity <;> norm_num

lemma cubic_natDegree (a : k) : (cubic a).natDegree = 3 := by
  unfold cubic
  compute_degree <;> norm_num

/-- Outer-variable evaluation at zero is the constant polynomial `-a³`. -/
@[simp] lemma cubic_eval_zero (a : k) : (cubic a).eval 0 = C (-(a ^ 3)) := by
  simp [cubic]

/-- Outer-variable evaluation at one is the constant polynomial `1-a³`. -/
@[simp] lemma cubic_eval_one (a : k) : (cubic a).eval 1 = C (1 - a ^ 3) := by
  simp [cubic]

/-- The zero-coordinate condition is exactly the required nonzero parameter. -/
lemma cubic_eval_zero_isUnit_iff (a : k) : IsUnit ((cubic a).eval 0) ↔ a ≠ 0 := by
  simp

/-- The complementary-coordinate condition is exactly `a³ ≠ 1`. -/
lemma cubic_eval_one_isUnit_iff (a : k) : IsUnit ((cubic a).eval 1) ↔ a ^ 3 ≠ 1 := by
  rw [cubic_eval_one, isUnit_C, isUnit_iff_ne_zero, sub_ne_zero, ne_comm]

lemma cubic_eval_zero_isUnit (a : k) (ha : a ≠ 0) : IsUnit ((cubic a).eval 0) := by
  rw [cubic_eval_zero]
  exact ((isUnit_iff_ne_zero.mpr (pow_ne_zero 3 ha)).neg).map C

lemma cubic_eval_one_isUnit (a : k) (ha : a ^ 3 ≠ 1) : IsUnit ((cubic a).eval 1) := by
  rw [cubic_eval_one]
  exact (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr ha.symm)).map C

/-- Parameter specialization, distinct from evaluating the outer variable. -/
@[simp] lemma cubic_specialize_zero (a : k) :
    (cubic a).map (evalRingHom 0) = cubicZero a := by simp [cubic, cubicZero]

@[simp] lemma cubic_specialize_one (a : k) :
    (cubic a).map (evalRingHom 1) = cubicOne a := by
  simp only [cubic, cubicOne, Polynomial.map_sub, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
    coe_evalRingHom, eval_mul, eval_X, eval_C, one_mul]
  rw [C_add, C_1]
  ring

/-- The actual cubic algebra has the three-vector monomial power basis. -/
def cubicPowerBasis (a : k) : PowerBasis k[X] (AdjoinRoot (cubic a)) :=
  AdjoinRoot.powerBasis' (cubic_monic a)

@[simp] lemma cubicPowerBasis_dim (a : k) : (cubicPowerBasis a).dim = 3 :=
  cubic_natDegree a

/-- Finite free, faithful, and faithfully flat, with both literal coordinates
invertible. The only restrictions are the two necessary outer evaluations. -/
lemma cubic_admissible (a : k) (h0 : a ≠ 0) (h1 : a ^ 3 ≠ 1) :
    Module.Finite k[X] (AdjoinRoot (cubic a)) ∧
      Module.Free k[X] (AdjoinRoot (cubic a)) ∧
      FaithfulSMul k[X] (AdjoinRoot (cubic a)) ∧
      Module.FaithfullyFlat k[X] (AdjoinRoot (cubic a)) ∧
      IsUnit (AdjoinRoot.root (cubic a)) ∧ IsUnit (1 - AdjoinRoot.root (cubic a)) := by
  have hd : 0 < (cubic a).natDegree := by rw [cubic_natDegree]; decide
  exact ⟨(finite_free (cubic_monic a)).1, (finite_free (cubic_monic a)).2,
    faithfulSMul (cubic_monic a) hd, faithfullyFlat (cubic_monic a) hd,
    by simpa using (rootUnit (cubic a) (cubic_eval_zero_isUnit a h0)).isUnit,
    AdjoinRoot.isUnit_one_sub_root_of_isUnit_eval_one _ (cubic_eval_one_isUnit a h1)⟩

/-- Scalar map to the literal zero endpoint. -/
def cubicEndpointZero (a : k) : AdjoinRoot (cubic a) →+* AdjoinRoot (cubicZero a) :=
  endpoint (cubic a) 0 (cubicZero a) (cubic_specialize_zero a)

/-- Scalar map to the literal one endpoint. -/
def cubicEndpointOne (a : k) : AdjoinRoot (cubic a) →+* AdjoinRoot (cubicOne a) :=
  endpoint (cubic a) 1 (cubicOne a) (cubic_specialize_one a)

/-- The whole zero tensor fiber is the cubic quotient. -/
def cubicFiberZeroEquiv (a : k) :
    Algebra.PolynomialFiber.Fiber (AdjoinRoot (cubic a)) (0 : k) ≃ₐ[k]
      AdjoinRoot (cubicZero a) :=
  endpointFiberEquiv (cubic a) 0 (cubicZero a) (cubic_specialize_zero a)

/-- The whole one tensor fiber is the product-polynomial quotient. -/
def cubicFiberOneEquiv (a : k) :
    Algebra.PolynomialFiber.Fiber (AdjoinRoot (cubic a)) (1 : k) ≃ₐ[k]
      AdjoinRoot (cubicOne a) :=
  endpointFiberEquiv (cubic a) 1 (cubicOne a) (cubic_specialize_one a)

@[simp] lemma cubicEndpointZero_root (a : k) :
    cubicEndpointZero a (AdjoinRoot.root (cubic a)) = AdjoinRoot.root (cubicZero a) :=
  endpoint_root _ _ _ _

@[simp] lemma cubicEndpointOne_root (a : k) :
    cubicEndpointOne a (AdjoinRoot.root (cubic a)) = AdjoinRoot.root (cubicOne a) :=
  endpoint_root _ _ _ _

@[simp] lemma cubicFiberZeroEquiv_root (a : k) :
    cubicFiberZeroEquiv a (Algebra.PolynomialFiber.specialize (AdjoinRoot (cubic a)) 0
      (AdjoinRoot.root (cubic a))) = AdjoinRoot.root (cubicZero a) :=
  endpointFiberEquiv_root _ _ _ _

@[simp] lemma cubicFiberOneEquiv_root (a : k) :
    cubicFiberOneEquiv a (Algebra.PolynomialFiber.specialize (AdjoinRoot (cubic a)) 1
      (AdjoinRoot.root (cubic a))) = AdjoinRoot.root (cubicOne a) :=
  endpointFiberEquiv_root _ _ _ _

@[simp] lemma cubicEndpointZero_one_sub_root (a : k) :
    cubicEndpointZero a (1 - AdjoinRoot.root (cubic a)) =
      1 - AdjoinRoot.root (cubicZero a) := by simp

@[simp] lemma cubicEndpointOne_one_sub_root (a : k) :
    cubicEndpointOne a (1 - AdjoinRoot.root (cubic a)) =
      1 - AdjoinRoot.root (cubicOne a) := by simp

@[simp] lemma cubicEndpointZero_of (a : k) (r : k[X]) :
    cubicEndpointZero a (AdjoinRoot.of (cubic a) r) =
      AdjoinRoot.of (cubicZero a) (r.eval 0) := endpoint_of _ _ _ _ _

@[simp] lemma cubicEndpointOne_of (a : k) (r : k[X]) :
    cubicEndpointOne a (AdjoinRoot.of (cubic a) r) =
      AdjoinRoot.of (cubicOne a) (r.eval 1) := endpoint_of _ _ _ _ _

lemma cubicFiberZeroEquiv_one_sub_root (a : k) :
    cubicFiberZeroEquiv a (Algebra.PolynomialFiber.specialize (AdjoinRoot (cubic a)) 0
      (1 - AdjoinRoot.root (cubic a))) = 1 - AdjoinRoot.root (cubicZero a) := by simp

lemma cubicFiberOneEquiv_one_sub_root (a : k) :
    cubicFiberOneEquiv a (Algebra.PolynomialFiber.specialize (AdjoinRoot (cubic a)) 1
      (1 - AdjoinRoot.root (cubic a))) = 1 - AdjoinRoot.root (cubicOne a) := by simp

@[simp] lemma cubicFiberZeroEquiv_of (a : k) (r : k[X]) :
    cubicFiberZeroEquiv a (Algebra.PolynomialFiber.specialize (AdjoinRoot (cubic a)) 0
      (AdjoinRoot.of (cubic a) r)) = AdjoinRoot.of (cubicZero a) (r.eval 0) :=
  endpointFiberEquiv_of _ _ _ _ _

@[simp] lemma cubicFiberOneEquiv_of (a : k) (r : k[X]) :
    cubicFiberOneEquiv a (Algebra.PolynomialFiber.specialize (AdjoinRoot (cubic a)) 1
      (AdjoinRoot.of (cubic a) r)) = AdjoinRoot.of (cubicOne a) (r.eval 1) :=
  endpointFiberEquiv_of _ _ _ _ _

end Polynomial.TwoUnitPolynomialFamily
