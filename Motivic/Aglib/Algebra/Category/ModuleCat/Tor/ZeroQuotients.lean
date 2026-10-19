/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Zeroth categorical Tor and tensor products of quotient rings

Right exactness of the actual tensor functor identifies its zeroth left
derived functor with tensor product. For two quotient rings the tensor
product is explicitly the quotient by the sum of the ideals. These are
constructed module isomorphisms, with no regularity or Tor-vanishing inputs.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct

universe u

section

variable {R : Type u} [CommRing R]

/-- The tensor product of two ring quotients is the quotient by their sum. -/
def _root_.Algebra.TensorProduct.tensorQuotientSupEquiv (I J : Ideal R) :
    (R ⧸ I) ⊗[R] (R ⧸ J) ≃ₗ[R] R ⧸ (I ⊔ J) :=
  let e := Algebra.TensorProduct.quotIdealMapEquivTensorQuot (R ⧸ I) J
  (e.symm.restrictScalars R).toLinearEquiv ≪≫ₗ
    (DoubleQuot.quotQuotEquivQuotSupₐ R I J).toLinearEquiv

/-- Zeroth categorical Tor is the actual tensor product, by right exactness. -/
def _root_.ModuleCat.TorComparison.torZeroIsoTensor (M N : ModuleCat.{u} R) :
    ((Tor (ModuleCat R) 0).obj M).obj N ≅ M ⊗ N :=
  (((tensoringLeft (ModuleCat R)).obj M).leftDerivedZeroIsoSelf).app N

end
