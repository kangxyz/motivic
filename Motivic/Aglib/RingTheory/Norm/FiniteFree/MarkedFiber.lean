/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.PolynomialFiberNorm
public import Mathlib.RingTheory.Norm.Basic
public import Motivic.Aglib.LinearAlgebra.Determinant.RankOne

/-!
# Finite-free norms on a full marked base scheme

A product decomposition after base change isolates a marked rank-one factor.
If the original element becomes one on the entire residual algebra, its norm
restricts to its marked value, including over nonreduced coefficient rings.
The decomposition and residual equality are explicit inputs, not existence claims.


Intended upstream module: `Aglib.RingTheory.Norm.FiniteFree.MarkedFiber`.
Incoming project consumers: `Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.MarkedFiber`.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Algebra

/-- The norm of a pair in a product of finite free algebras is the product of
its two norms. -/
theorem norm_prod_eq_mul
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    [Module.Finite R S] [Module.Free R S]
    [Module.Finite R T] [Module.Free R T] (s : S) (t : T) :
    norm R (s, t) = norm R s * norm R t := by
  have h : lmul R (S × T) (s, t) =
      LinearMap.prodMap (lmul R S s) (lmul R T t) := by
    ext x <;> rfl
  rw [norm_apply, h, LinearMap.det_prodMap]
  rfl

/-- A marked scalar and residual unit have the marked norm when the total
product is finite free. The residual algebra itself need not be free. -/
theorem norm_prod_mk_one
    {Q E : Type*} [CommRing Q] [CommRing E] [Algebra Q E]
    [Module.Finite Q (Q × E)] [Module.Free Q (Q × E)] (a : Q) :
    norm Q (a, (1 : E)) = a := by
  have h : lmul Q (Q × E) (a, 1) =
      LinearMap.id + (LinearMap.fst Q Q E).smulRight (a - 1, 0) := by
    apply LinearMap.ext
    intro x
    rcases x with ⟨x, y⟩
    apply Prod.ext
    · change a * x = x + x * (a - 1)
      ring
    · change 1 * y = y + x • (0 : E)
      simp
  rw [norm_apply, h, LinearMap.det_id_add_smulRight]
  simp

/-- A split marked factor computes the full nonreduced base-changed norm.
Only the original algebra is finite free; freeness of the residual factor is
neither required nor inferred. -/
theorem norm_eq_marked_value_of_split_baseChange
    {R Q S E : Type*} [CommRing R] [CommRing Q] [CommRing S] [CommRing E]
    [Algebra R Q] [Algebra R S] [Algebra Q E]
    [Module.Finite R S] [Module.Free R S]
    (e : (Q ⊗[R] S) ≃ₐ[Q] (Q × E)) (s : S) (a : Q)
    (h : e ((1 : Q) ⊗ₜ[R] s) = (a, 1)) :
    algebraMap R Q (norm R s) = a := by
  let : Module.Finite Q (Q × E) := Module.Finite.equiv e.toLinearEquiv
  let : Module.Free Q (Q × E) := Module.Free.of_equiv e.toLinearEquiv
  rw [← norm_one_tmul (A := Q), ← norm_eq_of_algEquiv e, h, norm_prod_mk_one]

/-- A full marked rank-one factor and residual value one determine the norm
on an arbitrary base algebra, without any reducedness hypothesis. -/
theorem norm_eq_marked_value_of_tensorProduct_equiv_prod
    {R Q S E : Type*} [CommRing R] [CommRing Q] [CommRing S] [CommRing E]
    [Algebra R Q] [Algebra R S] [Algebra Q E]
    [Module.Finite R S] [Module.Free R S]
    (e : (Q ⊗[R] S) ≃ₐ[Q] (Q × E)) (s : S) (a : Q)
    (h : e ((1 : Q) ⊗ₜ[R] s) = (a, 1)) :
    algebraMap R Q (norm R s) = a := by
  exact norm_eq_marked_value_of_split_baseChange e s a h

end Algebra
