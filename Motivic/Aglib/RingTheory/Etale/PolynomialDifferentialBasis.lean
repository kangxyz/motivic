/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Etale.DifferentialCriterion
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Prescribed polynomial coordinates from their actual differential basis -/

@[expose] public noncomputable section

open Module KaehlerDifferential

universe u v w

namespace Algebra.FormallyEtale

/-- A basis of the actual coordinate differentials proves formal étaleness of
that same polynomial map; coordinates are not reselected. -/
theorem of_polynomial_differential_basis
    (k : Type u) (R : Type v) (ι : Type w) [CommRing k] [CommRing R]
    [Algebra k R] [Algebra (MvPolynomial ι k) R]
    [IsScalarTower k (MvPolynomial ι k) R]
    [Subsingleton (H1Cotangent k R)]
    (b : Basis ι R Ω[R⁄k])
    (hb : ∀ j, b j = D k R (algebraMap (MvPolynomial ι k) R (.X j))) :
    FormallyEtale (MvPolynomial ι k) R := by
  let bP := (mvPolynomialBasis k ι).baseChange R
  have he : mapBaseChange k (MvPolynomial ι k) R =
      (bP.equiv b (Equiv.refl ι)).toLinearMap := by
    apply bP.ext
    intro j
    simp only [LinearEquiv.coe_coe, Basis.equiv_apply, Equiv.refl_apply, hb]
    simp [bP, mapBaseChange_tmul, map_D]
  apply FormallyEtale.of_bijective_mapBaseChange_of_subsingleton_h1 k (MvPolynomial ι k) R
  rw [he]
  exact (bP.equiv b (Equiv.refl ι)).bijective

end Algebra.FormallyEtale
