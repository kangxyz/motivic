/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.WeilRestriction.FiniteFree.Basic

/-!
# Universal coordinates for finite-free restriction of scalars

The maps use the literal scalar tensor product and the chosen finite basis.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct
open Module _root_.MvPolynomial

namespace Algebra.WeilRestriction

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable {ι κ σ : Type*} [Fintype κ]
variable {T T' : Type*} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T']

omit [Fintype κ] in
/-- Scalar extension maps act on each basis coordinate by the original map. -/
theorem repr_tensorMap (b : Basis κ A B) (h : T →ₐ[A] T') (x : T ⊗[A] B) (j : κ) :
    (b.baseChange T').repr (Algebra.TensorProduct.map h (AlgHom.id A B) x) j =
      h ((b.baseChange T).repr x j) := by
  induction x using TensorProduct.inductionOn with
  | tmul t z => simp [Basis.baseChange_repr_tmul]
  | add x y hx hy => simp [hx, hy]

/-- Reconstruct the tensor tuple from a homomorphism on scalar coordinates. -/
def tensorTuple (b : Basis κ A B) (h : CoordinateRing A ι κ →ₐ[A] T)
    (i : ι) : T ⊗[A] B :=
  Algebra.TensorProduct.map h (AlgHom.id A B) (universalGenerator b i)

/-- Recovering coordinates after reconstruction returns the original map. -/
theorem coordinateHom_tensorTuple (b : Basis κ A B)
    (h : CoordinateRing A ι κ →ₐ[A] T) : coordinateHom b (tensorTuple b h) = h := by
  ext p
  rcases p with ⟨i, j⟩
  simp only [coordinateHom, aeval_X, tensorTuple, repr_tensorMap]
  congr 1
  classical
  simp [universalGenerator, map_sum, Basis.baseChange_repr_tmul, Basis.repr_self,
    Finsupp.single_apply, ite_smul]

/-- Free polynomial coordinates represent tensor-valued tuples. -/
def coordinateEquiv (b : Basis κ A B) :
    (CoordinateRing A ι κ →ₐ[A] T) ≃ (ι → T ⊗[A] B) where
  toFun := tensorTuple b
  invFun := coordinateHom b
  left_inv := coordinateHom_tensorTuple b
  right_inv v := funext (coordinateHom_universalGenerator b v)

/-- The tuple equivalence is natural in the test algebra. -/
theorem tensorTuple_comp (b : Basis κ A B) (h : CoordinateRing A ι κ →ₐ[A] T)
    (g : T →ₐ[A] T') (i : ι) :
    tensorTuple b (g.comp h) i =
      Algebra.TensorProduct.map g (AlgHom.id A B) (tensorTuple b h i) := by
  simp [tensorTuple, universalGenerator]

/-- Evaluating all coefficient relations is exactly the original tensor equation. -/
theorem coefficientRelation_map_zero_iff (b : Basis κ A B)
    (f : σ → MvPolynomial ι B) (h : CoordinateRing A ι κ →ₐ[A] T) (s : σ) :
    (∀ j, h (coefficientRelation b f (s, j)) = 0) ↔
      Algebra.TensorProduct.map h (AlgHom.id A B) (substitution b (f s)) = 0 := by
  constructor
  · intro hzero
    apply (b.baseChange T).repr.injective
    apply Finsupp.ext
    intro j
    simpa only [map_zero, Finsupp.zero_apply, repr_tensorMap, coefficientRelation]
      using hzero j
  · intro hzero j
    have := congrArg (fun x => (b.baseChange T).repr x j) hzero
    simpa only [map_zero, Finsupp.zero_apply, repr_tensorMap, coefficientRelation] using this

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- A tensor tuple determines a polynomial homomorphism over the original coefficient algebra. -/
def polynomialHom (b : Basis κ A B) (h : CoordinateRing A ι κ →ₐ[A] T) :
    MvPolynomial ι B →ₐ[B] T ⊗[A] B :=
  aeval (tensorTuple b h)

/-- The polynomial homomorphism is evaluation of the literal universal substitution. -/
theorem polynomialHom_apply (b : Basis κ A B)
    (h : CoordinateRing A ι κ →ₐ[A] T) (p : MvPolynomial ι B) :
    polynomialHom b h p =
      Algebra.TensorProduct.map h (AlgHom.id A B) (substitution b p) := by
  have heq : (polynomialHom b h).toRingHom =
      (Algebra.TensorProduct.map h (AlgHom.id A B)).toRingHom.comp (substitution b) := by
    ext c <;> simp [polynomialHom, substitution, tensorTuple,
      Algebra.TensorProduct.algebraMap_eq_includeRight]
  exact DFunLike.congr_fun heq p

/-- The defining ideal is killed precisely when the original relations vanish. -/
theorem relationIdeal_le_ker_iff (b : Basis κ A B)
    (f : σ → MvPolynomial ι B) (h : CoordinateRing A ι κ →ₐ[A] T) :
    relationIdeal b f ≤ RingHom.ker h ↔ ∀ s, polynomialHom b h (f s) = 0 := by
  rw [relationIdeal, Ideal.span_le]
  constructor
  · intro hh s
    rw [polynomialHom_apply, ← coefficientRelation_map_zero_iff]
    intro j
    exact hh ⟨(s, j), rfl⟩
  · intro hh p hp
    obtain ⟨⟨s, j⟩, rfl⟩ := hp
    exact (coefficientRelation_map_zero_iff b f h s).mpr
      ((polynomialHom_apply b h (f s)) ▸ hh s) j

end Algebra.WeilRestriction
