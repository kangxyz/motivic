/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.PolynomialFiberNorm
public import Mathlib.RingTheory.DualNumber
public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.Algebra.Group.TypeTags.Hom

/-!
# Consumers of polynomial-fiber norm invariance

The square-zero example is the actual evaluation fiber of `k[X][ε]`, with
a nonzero nilpotent in each fiber. Signed statements use the existing norm
on units, in `Additive kˣ`. They do not assert a motivic chain-map comparison.
-/

@[expose] public section

noncomputable section

open Polynomial
open scoped TensorProduct
open Algebra.PolynomialFiber

namespace MotivicTest.PolynomialFiberNorm

universe u v

variable {k : Type u} [Field k]

/-- The polynomial dual-number algebra is genuinely finite free. -/
theorem dualPolynomial_finiteFree :
    Module.Finite k[X] (DualNumber k[X]) ∧ Module.Free k[X] (DualNumber k[X]) :=
  ⟨inferInstanceAs (Module.Finite k[X] (k[X] × k[X])),
    inferInstanceAs (Module.Free k[X] (k[X] × k[X]))⟩

/-- The actual nilpotent epsilon remains nonzero in every evaluation fiber. -/
theorem dualFiber_nonreduced (a : k) :
    specialize (DualNumber k[X]) a DualNumber.eps ≠ 0 ∧
      specialize (DualNumber k[X]) a DualNumber.eps ^ 2 = 0 := by
  constructor
  · let := evaluationAlgebra a
    let e : Module.Basis (Fin 2) k[X] (DualNumber k[X]) := Module.Basis.finTwoProd k[X]
    have hrepr : (e.baseChange k).repr (specialize (DualNumber k[X]) a DualNumber.eps) 1 = 1 := by
      change (e.baseChange k).repr (1 ⊗ₜ[k[X]] DualNumber.eps) 1 = 1
      rw [Module.Basis.baseChange_repr_tmul]
      have hcoord : e.repr DualNumber.eps 1 = 1 := by
        exact congrFun (Module.Basis.coe_finTwoProd_repr (DualNumber.eps : DualNumber k[X])) 1
      rw [hcoord, one_smul]
    intro hzero
    rw [hzero, map_zero, Finsupp.zero_apply] at hrepr
    exact zero_ne_one hrepr
  · rw [← map_pow, DualNumber.eps_pow_two, map_zero]

/-- The polynomial-valued determinant norm sees both dimensions, retaining
the nilpotent coefficient rather than passing to a reduced quotient. -/
theorem dualPolynomial_norm (x : DualNumber k[X]) :
    Algebra.norm k[X] x = x.fst ^ 2 := by
  let e : Module.Basis (Fin 2) k[X] (DualNumber k[X]) := Module.Basis.finTwoProd k[X]
  rw [Algebra.norm_eq_matrix_det e, Matrix.det_fin_two]
  rw [Algebra.leftMulMatrix_eq_repr_mul e x 0 0,
    Algebra.leftMulMatrix_eq_repr_mul e x 1 1,
    Algebra.leftMulMatrix_eq_repr_mul e x 0 1,
    Algebra.leftMulMatrix_eq_repr_mul e x 1 0]
  have h0 : e 0 = 1 := Module.Basis.finTwoProd_zero k[X]
  have h1 : e 1 = DualNumber.eps := Module.Basis.finTwoProd_one k[X]
  have hr0 (y : DualNumber k[X]) : e.repr y 0 = y.fst :=
    congrFun (Module.Basis.coe_finTwoProd_repr y) 0
  have hr1 (y : DualNumber k[X]) : e.repr y 1 = y.snd :=
    congrFun (Module.Basis.coe_finTwoProd_repr y) 1
  rw [h0, h1, hr0, hr1, hr0, hr1]
  simp [pow_two]

/-- The determinant norm of the actual nonreduced fiber is the square of
the evaluated constant coordinate, for arbitrary elements. -/
theorem dualFiber_norm (a : k) (x : DualNumber k[X]) :
    Algebra.norm k (specialize (DualNumber k[X]) a x) = (x.fst.eval a) ^ 2 := by
  let : Module.Free k[X] (DualNumber k[X]) := dualPolynomial_finiteFree.2
  let : Module.Finite k[X] (DualNumber k[X]) := dualPolynomial_finiteFree.1
  rw [norm_specialize, dualPolynomial_norm, Polynomial.eval_pow]

/-- A nonconstant unit with a nonzero nilpotent polynomial coefficient. -/
def varyingDualUnit : (DualNumber k[X])ˣ where
  val := 1 + TrivSqZeroExt.inr X
  inv := 1 - TrivSqZeroExt.inr X
  val_inv := by ext <;> simp
  inv_val := by ext <;> simp

/-- Both endpoints of the nonconstant unit have determinant norm one. -/
theorem varyingDualUnit_norm (a : k) :
    Algebra.norm k
      (specialize (DualNumber k[X]) a (varyingDualUnit (k := k) : DualNumber k[X])) = 1 := by
  rw [dualFiber_norm]
  simp [varyingDualUnit]

/-- The all-branch local-length formula applies to these genuinely
nonreduced fibers at the two literal endpoints. -/
theorem dualFiber_weighted_endpoints
    [Fintype (MaximalSpectrum (Fiber (DualNumber k[X]) (0 : k)))]
    [Fintype (MaximalSpectrum (Fiber (DualNumber k[X]) (1 : k)))] :
    (∏ p : MaximalSpectrum (Fiber (DualNumber k[X]) (0 : k)),
      Algebra.norm k (Ideal.Quotient.mk p.asIdeal
        (specialize (DualNumber k[X]) 0 (varyingDualUnit (k := k) : DualNumber k[X]))) ^
        (Module.length (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal)).toNat) =
    ∏ p : MaximalSpectrum (Fiber (DualNumber k[X]) (1 : k)),
      Algebra.norm k (Ideal.Quotient.mk p.asIdeal
        (specialize (DualNumber k[X]) 1 (varyingDualUnit (k := k) : DualNumber k[X]))) ^
        (Module.length (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal)).toNat := by
  let : Module.Free k[X] (DualNumber k[X]) := dualPolynomial_finiteFree.2
  let : Module.Finite k[X] (DualNumber k[X]) := dualPolynomial_finiteFree.1
  exact prod_residue_norm_eq (k := k) (B := DualNumber k[X])
    (varyingDualUnit (k := k)) 0 1


/-- Both independent branches survive the determinant base-change formula
for the disconnected polynomial algebra. -/
theorem productFiber_norm (a : k) (p q : k[X]) :
    Algebra.norm k (specialize (k[X] × k[X]) a (p, q)) = p.eval a * q.eval a := by
  rw [norm_specialize]
  have hnorm : Algebra.norm k[X] (p, q) = p * q := by
    rw [Algebra.norm_apply]
    have hmul : Algebra.lmul k[X] (k[X] × k[X]) (p, q) =
        (LinearMap.mulLeft k[X] p).prodMap (LinearMap.mulLeft k[X] q) := by
      ext x <;> rfl
    rw [hmul, LinearMap.det_prodMap, LinearMap.det_mulLeft, LinearMap.det_mulLeft]
  rw [hnorm, Polynomial.eval_mul]

/-- The actual length-weighted product in each disconnected fiber equals
the product of the two evaluated branch values. -/
theorem productFiber_weighted (a : k)
    [Fintype (MaximalSpectrum (Fiber (k[X] × k[X]) a))] (p q : k[X]) :
    (∏ m : MaximalSpectrum (Fiber (k[X] × k[X]) a),
      Algebra.norm k (Ideal.Quotient.mk m.asIdeal (specialize (k[X] × k[X]) a (p, q))) ^
        (Module.length (Localization.AtPrime m.asIdeal)
          (Localization.AtPrime m.asIdeal)).toNat) = p.eval a * q.eval a := by
  rw [← norm_specialize_eq_prod]
  exact productFiber_norm a p q

variable {B : Type v} [CommRing B] [Algebra k[X] B]
  [Module.Free k[X] B] [Module.Finite k[X] B]

/-- The unshifted endpoint sign is fiber zero minus fiber one. -/
theorem unshifted_endpoint_norm (u : Bˣ) :
    Additive.ofMul (Units.map (Algebra.norm k)
        (Units.map (specialize B (0 : k)).toMonoidHom u)) -
      Additive.ofMul (Units.map (Algebra.norm k)
        (Units.map (specialize B (1 : k)).toMonoidHom u)) = 0 := by
  rw [normUnits_specialize_eq u 0 1, sub_self]

/-- The weight-one signed endpoint expression is the negative of fiber
zero minus fiber one, hence also vanishes in the actual base unit group. -/
theorem signed_endpoint_norm (u : Bˣ) :
    -(Additive.ofMul (Units.map (Algebra.norm k)
        (Units.map (specialize B (0 : k)).toMonoidHom u)) -
      Additive.ofMul (Units.map (Algebra.norm k)
        (Units.map (specialize B (1 : k)).toMonoidHom u))) = 0 := by
  rw [unshifted_endpoint_norm, neg_zero]

open Lean in
run_cmd do
  for name in #[``Algebra.norm_one_tmul,
      ``Algebra.PolynomialFiber.norm_specialize,
      ``Algebra.PolynomialFiber.norm_unit_eq_C,
      ``Algebra.PolynomialFiber.norm_specialize_eq,
      ``Algebra.PolynomialFiber.normUnits_specialize_eq,
      ``Algebra.PolynomialFiber.norm_specialize_eq_of_torsionFree,
      ``Algebra.PolynomialFiber.norm_specialize_eq_prod,
      ``Algebra.PolynomialFiber.prod_residue_norm_eq,
      ``Algebra.PolynomialFiber.prod_residue_norm_eq_of_finite,
      ``dualPolynomial_finiteFree, ``dualFiber_nonreduced,
      ``dualPolynomial_norm, ``dualFiber_norm, ``varyingDualUnit_norm,
      ``dualFiber_weighted_endpoints, ``productFiber_norm, ``productFiber_weighted,
      ``unshifted_endpoint_norm, ``signed_endpoint_norm] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Polynomial-fiber norm and signed-endpoint audit passed: standard foundations only."

end MotivicTest.PolynomialFiberNorm
