/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Ideal.GoingDown.BaseChange

/-!
# Consumers of finite-type going-down base change

The source extension is an integral inclusion of a normal domain into a
domain. The algebra used for base change is unrestricted apart from finite
type: examples include a product, a square-zero polynomial quotient, and
a zero ring. No domain property is imposed on any tensor product.
-/

@[expose] public section

open scoped TensorProduct Polynomial

universe u v w x

namespace MotivicTest.GoingDownBaseChange

section TensorProduct

variable {R : Type u} {S : Type v} {P : Type w} {A : Type x}
  [CommRing R] [CommRing S] [CommRing P] [CommRing A]
  [Algebra R S] [Algebra R P] [Algebra R A]
  [Algebra.HasGoingDown P (P ⊗[R] S)]

/-- Quotient descent needs only the supplied going-down property. -/
theorem quotient_tensor (I : Ideal P) :
    Algebra.HasGoingDown (P ⧸ I) ((P ⧸ I) ⊗[R] S) :=
  Algebra.HasGoingDown.tensor_quotient I

/-- Arbitrary surjective presentations retain the canonical tensor algebra. -/
theorem surjective_tensor (f : P →ₐ[R] A) (hf : Function.Surjective f) :
    Algebra.HasGoingDown A (A ⊗[R] S) :=
  Algebra.HasGoingDown.tensor_of_surjective f hf

/-- The tensor-algebra structural map is the original left-factor inclusion. -/
theorem tensor_algebraMap (a : A) :
    algebraMap A (A ⊗[R] S) a = a ⊗ₜ[R] (1 : S) := rfl

end TensorProduct

/-- Polynomial normality has only the original normal-domain premises. -/
theorem polynomial_normal (R : Type u) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] (n : ℕ) : IsIntegrallyClosed (MvPolynomial (Fin n) R) :=
  MvPolynomial.isIntegrallyClosed_fin n

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- The polynomial algebra map is the actual coefficient map. -/
theorem polynomial_algebraMap {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S] (n : ℕ) (p : MvPolynomial (Fin n) R) :
    algebraMap (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) S) p =
      MvPolynomial.map (algebraMap R S) p := rfl


variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
  [Algebra R S] [IsDomain S] [FaithfulSMul R S]
  [Algebra.IsIntegral R S] [IsIntegrallyClosed R]

/-- The original coefficient-map polynomial extension satisfies going down. -/
theorem polynomial_goingDown (n : ℕ) :
    Algebra.HasGoingDown (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) S) :=
  Algebra.HasGoingDown.mvPolynomial_fin n

/-- Polynomial tensor transport retains the literal scalar-extension algebra. -/
theorem polynomial_tensor (n : ℕ) :
    Algebra.HasGoingDown (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R ⊗[R] S) :=
  Algebra.HasGoingDown.mvPolynomial_tensor n

/-- Going down holds for the actual tensor-product map of any finite-type algebra. -/
theorem finiteType_algebra (A : Type w) [CommRing A] [Algebra R A] [Algebra.FiniteType R A] :
    Algebra.HasGoingDown A (A ⊗[R] S) :=
  Algebra.HasGoingDown.finiteType_baseChange

/-- A product base change is allowed, so no domain hypothesis is hidden in the base. -/
theorem product_algebra : Algebra.HasGoingDown (R × R) ((R × R) ⊗[R] S) :=
  Algebra.HasGoingDown.finiteType_baseChange

/-- The base may have nilpotents: the square-zero polynomial quotient is allowed. -/
theorem square_zero_quotient :
    Algebra.HasGoingDown (R[X] ⧸ Ideal.span {(Polynomial.X : R[X]) ^ 2})
      ((R[X] ⧸ Ideal.span {(Polynomial.X : R[X]) ^ 2}) ⊗[R] S) :=
  Algebra.HasGoingDown.finiteType_baseChange

/-- Even the zero algebra is allowed as a finite-type base change. -/
theorem zero_algebra :
    Algebra.HasGoingDown (R ⧸ (⊤ : Ideal R)) ((R ⧸ (⊤ : Ideal R)) ⊗[R] S) :=
  Algebra.HasGoingDown.finiteType_baseChange

end MotivicTest.GoingDownBaseChange
