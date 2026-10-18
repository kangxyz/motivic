/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Extension.Presentation.Basic

/-!
# Coefficient equations for affine finite-free restriction of scalars

The coefficient quotient below is constructed from actual polynomial relations.
Its finite presentation does not require the base algebra to be étale. The
universal-property and étaleness stages are separate from this construction.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct
open Module MvPolynomial

namespace Algebra.WeilRestriction

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable {ι κ σ : Type*} [Fintype κ]

/-- One scalar-coordinate variable for each generator and basis vector. -/
abbrev CoordinateRing (A : Type*) [CommRing A] (ι κ : Type*) :=
  MvPolynomial (ι × κ) A

/-- The generic element attached to a generator, expanded in the chosen basis. -/
def universalGenerator (b : Basis κ A B) (i : ι) :
    CoordinateRing A ι κ ⊗[A] B :=
  ∑ j, X (i, j) ⊗ₜ[A] b j

/-- Substitute generic basis expansions into the original polynomial ring. -/
def substitution (b : Basis κ A B) :
    MvPolynomial ι B →+* CoordinateRing A ι κ ⊗[A] B :=
  eval₂Hom Algebra.TensorProduct.includeRight.toRingHom (universalGenerator b)

/-- Every basis coefficient of every substituted relation is imposed. -/
def coefficientRelation (b : Basis κ A B) (f : σ → MvPolynomial ι B)
    (p : σ × κ) : CoordinateRing A ι κ :=
  (b.baseChange (CoordinateRing A ι κ)).repr (substitution b (f p.1)) p.2

/-- The ideal of all coefficient equations, including nilpotent information. -/
def relationIdeal (b : Basis κ A B) (f : σ → MvPolynomial ι B) :
    Ideal (CoordinateRing A ι κ) :=
  Ideal.span (Set.range (coefficientRelation b f))

/-- The concrete coefficient quotient, prior to its representability theorem. -/
abbrev CoordinateQuotient (b : Basis κ A B) (f : σ → MvPolynomial ι B) :=
  CoordinateRing A ι κ ⧸ relationIdeal b f

/-- Finitely many original relations give finitely many coefficient relations. -/
theorem relationIdeal_fg [Finite σ] (b : Basis κ A B)
    (f : σ → MvPolynomial ι B) : (relationIdeal b f).FG := by
  exact Submodule.fg_span (Set.finite_range (coefficientRelation b f))

instance [Finite ι] [Finite σ] (b : Basis κ A B) (f : σ → MvPolynomial ι B) :
    FinitePresentation A (CoordinateQuotient b f) :=
  FinitePresentation.quotient (relationIdeal_fg b f)

/-- Vanishing is tested in every coordinate of the entire tensor element. -/
theorem substitution_eq_zero_iff (b : Basis κ A B)
    (f : σ → MvPolynomial ι B) (s : σ) :
    substitution b (f s) = 0 ↔ ∀ j, coefficientRelation b f (s, j) = 0 := by
  constructor
  · intro h j
    simp [coefficientRelation, h]
  · intro h
    apply (b.baseChange (CoordinateRing A ι κ)).repr.injective
    apply Finsupp.ext
    intro j
    simpa [coefficientRelation] using h j

variable {T : Type*} [CommRing T] [Algebra A T]

/-- The scalar coordinates of a tuple of actual tensor-valued generators. -/
def coordinateHom (b : Basis κ A B) (v : ι → T ⊗[A] B) :
    CoordinateRing A ι κ →ₐ[A] T :=
  aeval fun p => (b.baseChange T).repr (v p.1) p.2

/-- Applying the coordinate homomorphism recovers the specified tensor tuple. -/
theorem coordinateHom_universalGenerator (b : Basis κ A B) (v : ι → T ⊗[A] B)
    (i : ι) :
    Algebra.TensorProduct.map (coordinateHom b v) (AlgHom.id A B)
      (universalGenerator b i) = v i := by
  simp only [universalGenerator, map_sum, Algebra.TensorProduct.map_tmul,
    coordinateHom, aeval_X, AlgHom.id_apply]
  simpa only [Basis.baseChange_apply, TensorProduct.smul_tmul',
    smul_eq_mul, mul_one] using (b.baseChange T).sum_repr (v i)

end Algebra.WeilRestriction
