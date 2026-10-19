/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.PolynomialFiberNorm
public import Mathlib.RingTheory.AdjoinRoot

/-!
# Monic polynomial interpolation with an invertible coordinate

For any field, a monic polynomial of positive degree and nonzero constant
coefficient admits the literal interpolation to `(T - 1)^(d - 1) * (T - a)`,
where `a = (-1)^d * p.coeff 0`. The family is monic of degree `d`, has a
constant unit constant coefficient, and defines an actual finite free
`AdjoinRoot` algebra with invertible `T`.

This is an algebra prerequisite. It does not construct a fundamental
correspondence, identify its endpoint cycles, or compute motivic cohomology.
No reducedness, separability, or splitting hypothesis is used.
-/

@[expose] public section

noncomputable section

open Polynomial
open scoped TensorProduct

namespace Polynomial.MonicUnitInterpolation

universe u

variable {k : Type u} [Field k]

/-- The determinant-norm candidate, retaining the degree sign. -/
def normValue (p : k[X]) : k := (-1) ^ p.natDegree * p.coeff 0

/-- The split endpoint, including its repeated identity factor. -/
def target (p : k[X]) : k[X] :=
  (X - C 1) ^ (p.natDegree - 1) * (X - C (normValue p))

/-- Linear interpolation in the inner parameter `s`, with outer variable `T`. -/
def interpolate (p q : k[X]) : k[X][X] :=
  C (1 - X) * p.map C + C X * q.map C

/-- The actual family joining a polynomial to its split endpoint. -/
def family (p : k[X]) : k[X][X] := interpolate p (target p)

lemma target_monic (p : k[X]) : (target p).Monic :=
  ((monic_X_sub_C 1).pow _).mul (monic_X_sub_C _)

lemma target_natDegree (p : k[X]) (hd : 1 ≤ p.natDegree) :
    (target p).natDegree = p.natDegree := by
  simp only [target, Monic.natDegree_mul ((monic_X_sub_C (1 : k)).pow _)
    (monic_X_sub_C _), natDegree_pow, natDegree_X_sub_C, mul_one]
  exact Nat.sub_add_cancel hd

lemma target_coeff_zero (p : k[X]) (hd : 1 ≤ p.natDegree) :
    (target p).coeff 0 = p.coeff 0 := by
  simp only [coeff_zero_eq_eval_zero, target, eval_mul, eval_pow, eval_sub, eval_X,
    eval_C, zero_sub, normValue]
  have hd' : p.natDegree - 1 + 1 = p.natDegree := Nat.sub_add_cancel hd
  calc
    (-1 : k) ^ (p.natDegree - 1) * -((-1) ^ p.natDegree * p.eval 0) =
        ((-1) ^ (p.natDegree - 1) * (-1)) *
          ((-1) ^ p.natDegree * p.eval 0) := by ring
    _ = ((-1 : k) ^ p.natDegree * (-1) ^ p.natDegree) * p.eval 0 := by
      rw [← pow_succ, hd', mul_assoc]
    _ = p.eval 0 := by rw [← mul_pow]; simp

lemma normValue_ne_zero (p : k[X]) (h0 : p.coeff 0 ≠ 0) : normValue p ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) h0

lemma interpolate_coeff (p q : k[X]) (n : ℕ) :
    (interpolate p q).coeff n = (1 - X) * C (p.coeff n) + X * C (q.coeff n) := by
  simp only [interpolate, coeff_add, coeff_C_mul, coeff_map]

lemma interpolate_monic_natDegree {p q : k[X]} (hp : p.Monic) (hq : q.Monic)
    (hdeg : q.natDegree = p.natDegree) :
    (interpolate p q).Monic ∧ (interpolate p q).natDegree = p.natDegree := by
  have hle : (interpolate p q).natDegree ≤ p.natDegree := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    rw [interpolate_coeff, coeff_eq_zero_of_natDegree_lt hn,
      coeff_eq_zero_of_natDegree_lt (hdeg ▸ hn)]
    simp
  have hcoeff : (interpolate p q).coeff p.natDegree = 1 := by
    rw [interpolate_coeff, hp.coeff_natDegree, ← hdeg, hq.coeff_natDegree]
    simp
  exact ⟨monic_of_natDegree_le_of_coeff_eq_one _ hle hcoeff,
    natDegree_eq_of_le_of_coeff_ne_zero hle (hcoeff.trans_ne one_ne_zero)⟩

lemma interpolate_coeff_zero {p q : k[X]} (h0 : q.coeff 0 = p.coeff 0) :
    (interpolate p q).coeff 0 = C (p.coeff 0) := by
  rw [interpolate_coeff, h0]
  ring

lemma interpolate_specialize (p q : k[X]) (s : k) :
    (interpolate p q).map (evalRingHom s) = C (1 - s) * p + C s * q := by
  simp only [interpolate, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
    coe_evalRingHom, eval_sub, eval_one, eval_X, Polynomial.map_map]
  have h : (evalRingHom s).comp C = RingHom.id k := by ext; simp
  simp only [h, Polynomial.map_id]

@[simp] lemma interpolate_specialize_zero (p q : k[X]) :
    (interpolate p q).map (evalRingHom (0 : k)) = p := by
  simp [interpolate_specialize]

@[simp] lemma interpolate_specialize_one (p q : k[X]) :
    (interpolate p q).map (evalRingHom (1 : k)) = q := by
  simp [interpolate_specialize]

lemma family_monic_natDegree {p : k[X]} (hp : p.Monic) (hd : 1 ≤ p.natDegree) :
    (family p).Monic ∧ (family p).natDegree = p.natDegree :=
  interpolate_monic_natDegree hp (target_monic p) (target_natDegree p hd)

lemma family_monic {p : k[X]} (hp : p.Monic) (hd : 1 ≤ p.natDegree) :
    (family p).Monic := (family_monic_natDegree hp hd).1

lemma family_natDegree {p : k[X]} (hp : p.Monic) (hd : 1 ≤ p.natDegree) :
    (family p).natDegree = p.natDegree := (family_monic_natDegree hp hd).2

lemma family_coeff_zero (p : k[X]) (hd : 1 ≤ p.natDegree) :
    (family p).coeff 0 = C (p.coeff 0) :=
  interpolate_coeff_zero (target_coeff_zero p hd)

lemma family_coeff_zero_isUnit (p : k[X]) (hd : 1 ≤ p.natDegree)
    (h0 : p.coeff 0 ≠ 0) : IsUnit ((family p).coeff 0) := by
  rw [family_coeff_zero p hd]
  exact (isUnit_iff_ne_zero.mpr h0).map C

@[simp] lemma family_specialize_zero (p : k[X]) :
    (family p).map (evalRingHom (0 : k)) = p :=
  interpolate_specialize_zero p (target p)

@[simp] lemma family_specialize_one (p : k[X]) :
    (family p).map (evalRingHom (1 : k)) = target p :=
  interpolate_specialize_one p (target p)

/-- The literal quotient `k[s][T]/(family p)`, not its reduction. -/
abbrev FamilyAlgebra (p : k[X]) := AdjoinRoot (family p)

/-- The actual power basis of the monic quotient. -/
def familyPowerBasis {p : k[X]} (hp : p.Monic) (hd : 1 ≤ p.natDegree) :
    PowerBasis k[X] (FamilyAlgebra p) :=
  AdjoinRoot.powerBasis' (family_monic hp hd)

lemma familyPowerBasis_dim {p : k[X]} (hp : p.Monic) (hd : 1 ≤ p.natDegree) :
    (familyPowerBasis hp hd).dim = p.natDegree := family_natDegree hp hd

lemma family_free {p : k[X]} (hp : p.Monic) (hd : 1 ≤ p.natDegree) :
    Module.Free k[X] (FamilyAlgebra p) := (family_monic hp hd).free_adjoinRoot

lemma family_finite {p : k[X]} (hp : p.Monic) (hd : 1 ≤ p.natDegree) :
    Module.Finite k[X] (FamilyAlgebra p) := (family_monic hp hd).finite_adjoinRoot

/-- A unit constant coefficient makes the adjoined coordinate invertible,
even when the polynomial or quotient is nonreduced. -/
lemma adjoinRoot_root_isUnit {R : Type*} [CommRing R] (f : R[X])
    (h0 : IsUnit (f.coeff 0)) : IsUnit (AdjoinRoot.root f) := by
  have hrel : AdjoinRoot.root f * AdjoinRoot.mk f f.divX = -AdjoinRoot.of f (f.coeff 0) := by
    have h := congrArg (AdjoinRoot.mk f) (X_mul_divX_add f)
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [map_add, map_mul, AdjoinRoot.mk_self, AdjoinRoot.root,
      AdjoinRoot.of, RingHom.comp_apply] using h
  have hu : IsUnit (AdjoinRoot.root f * AdjoinRoot.mk f f.divX) := by
    rw [hrel]
    exact (h0.map (AdjoinRoot.of f)).neg
  exact (IsUnit.mul_iff.mp hu).1

/-- The outer coordinate is a unit in the actual family algebra. -/
def coordinateUnit (p : k[X]) (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0) :
    (FamilyAlgebra p)ˣ :=
  (adjoinRoot_root_isUnit (family p) (family_coeff_zero_isUnit p hd h0)).unit

@[simp] lemma coordinateUnit_val (p : k[X]) (hd : 1 ≤ p.natDegree)
    (h0 : p.coeff 0 ≠ 0) : (coordinateUnit p hd h0 : FamilyAlgebra p) =
      AdjoinRoot.root (family p) := IsUnit.unit_spec _

/-- Actual quotient homomorphism at parameter zero. -/
def endpointZero (p : k[X]) : FamilyAlgebra p →+* AdjoinRoot p :=
  AdjoinRoot.map (evalRingHom 0) (family p) p (by simp)

/-- Actual quotient homomorphism at parameter one. -/
def endpointOne (p : k[X]) : FamilyAlgebra p →+* AdjoinRoot (target p) :=
  AdjoinRoot.map (evalRingHom 1) (family p) (target p) (by simp)

@[simp] lemma endpointZero_root (p : k[X]) :
    endpointZero p (AdjoinRoot.root (family p)) = AdjoinRoot.root p :=
  AdjoinRoot.map_root _ _ _ _

@[simp] lemma endpointOne_root (p : k[X]) :
    endpointOne p (AdjoinRoot.root (family p)) = AdjoinRoot.root (target p) :=
  AdjoinRoot.map_root _ _ _ _

@[simp] lemma endpointZero_of (p : k[X]) (r : k[X]) :
    endpointZero p (AdjoinRoot.of (family p) r) = AdjoinRoot.of p (r.eval 0) :=
  AdjoinRoot.map_of _ _ _ _ _

@[simp] lemma endpointOne_of (p : k[X]) (r : k[X]) :
    endpointOne p (AdjoinRoot.of (family p) r) = AdjoinRoot.of (target p) (r.eval 1) :=
  AdjoinRoot.map_of _ _ _ _ _

/-- Base change of the literal quotient is the quotient by the specialized
polynomial. This includes all nilpotents and all components of the fiber. -/
def fiberEquiv (f : k[X][X]) (s : k) :
    Algebra.PolynomialFiber.Fiber (AdjoinRoot f) s ≃ₐ[k]
      AdjoinRoot (f.map (evalRingHom s)) := by
  let := Algebra.PolynomialFiber.evaluationAlgebra s
  let e : k ⊗[k[X]] k[X] ≃ₐ[k] k := Algebra.TensorProduct.rid k[X] k k
  exact (AdjoinRoot.tensorAlgEquiv f _ rfl).trans
    (AdjoinRoot.mapAlgEquiv e _ _ (by
      apply Associated.of_eq
      rw [Polynomial.map_map]
      congr 1
      apply RingHom.ext
      intro r
      change e (1 ⊗ₜ[k[X]] r) = r.eval s
      rw [Algebra.TensorProduct.rid_tmul, Algebra.smul_def, mul_one]
      rfl))

@[simp] lemma fiberEquiv_root (f : k[X][X]) (s : k) :
    fiberEquiv f s (Algebra.PolynomialFiber.specialize (AdjoinRoot f) s
      (AdjoinRoot.root f)) = AdjoinRoot.root (f.map (evalRingHom s)) := by
  let := Algebra.PolynomialFiber.evaluationAlgebra s
  change fiberEquiv f s (1 ⊗ₜ[k[X]] AdjoinRoot.root f) = _
  dsimp only [fiberEquiv]
  rw [AlgEquiv.trans_apply, AdjoinRoot.tensorAlgEquiv_root,
    AdjoinRoot.coe_mapAlgEquiv, AdjoinRoot.map_root]

/-- The whole zero fiber, as an algebra, is exactly the original quotient. -/
def fiberZeroEquiv (p : k[X]) :
    Algebra.PolynomialFiber.Fiber (FamilyAlgebra p) (0 : k) ≃ₐ[k] AdjoinRoot p :=
  (fiberEquiv (family p) 0).trans
    (AdjoinRoot.algEquivOfEq k _ _ (family_specialize_zero p))

/-- The whole one fiber is exactly the split quotient, without reduction. -/
def fiberOneEquiv (p : k[X]) :
    Algebra.PolynomialFiber.Fiber (FamilyAlgebra p) (1 : k) ≃ₐ[k]
      AdjoinRoot (target p) :=
  (fiberEquiv (family p) 1).trans
    (AdjoinRoot.algEquivOfEq k _ _ (family_specialize_one p))

@[simp] lemma fiberZeroEquiv_root (p : k[X]) :
    fiberZeroEquiv p (Algebra.PolynomialFiber.specialize (FamilyAlgebra p) 0
      (AdjoinRoot.root (family p))) = AdjoinRoot.root p := by
  simp [fiberZeroEquiv, AdjoinRoot.algEquivOfEq_root]

@[simp] lemma fiberOneEquiv_root (p : k[X]) :
    fiberOneEquiv p (Algebra.PolynomialFiber.specialize (FamilyAlgebra p) 1
      (AdjoinRoot.root (family p))) = AdjoinRoot.root (target p) := by
  simp [fiberOneEquiv, AdjoinRoot.algEquivOfEq_root]

end Polynomial.MonicUnitInterpolation
