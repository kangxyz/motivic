/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.AffineTorusPrimePolynomial
public import Motivic.Aglib.RingTheory.NormalMonicFactorization

/-! # Recovering the actual normalized rational function of an affine torus cycle -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent
open Polynomial.BoundaryOneRationalFunctions

universe u

namespace Motivic.AffineTorusPolynomialPresentation

variable {k R : Type u} [Field k] [CommRing R] [Algebra k R]
  [IsDomain R] [Algebra.Smooth k R]

/-- Multiplying the original generators' monic equations with their signed
multiplicities gives an actual localized rational function. -/
def cycleRationalFunction :
    FiniteCorrespondence (baseMap k R) (laurentProjection (.of k)) →+
      Additive (admissibleGroup R) :=
  Finsupp.liftAddHom (M := ℤ) (N := Additive (admissibleGroup R)) fun Z : Generator k R =>
    zmultiplesHom (Additive (admissibleGroup R)) (Additive.ofMul (generatorRationalFunction Z))

@[simp] theorem cycleRationalFunction_single (Z : Generator k R) (n : ℤ) :
    cycleRationalFunction (Finsupp.single Z n) =
      n • Additive.ofMul (generatorRationalFunction Z) :=
  Finsupp.liftAddHom_apply_single _ _ _

@[simp] theorem cycleRationalFunction_cycle (Z : Generator k R) :
    cycleRationalFunction Z.cycle = Additive.ofMul (generatorRationalFunction Z) := by
  rw [FiniteCorrespondenceGenerator.cycle, cycleRationalFunction_single, one_zsmul]

variable [IsNoetherianRing R]

/-- Recovering a cycle from its actual defining rational function is exact on
all original signed finite correspondences. -/
@[simp] theorem rationalDivisorHom_cycleRationalFunction
    (z : FiniteCorrespondence (baseMap k R) (laurentProjection (.of k))) :
    rationalDivisorHom (cycleRationalFunction z) = z := by
  classical
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | single Z n =>
    rw [cycleRationalFunction_single, map_zsmul]
    change n • rationalDivisor (generatorRationalFunction Z) = _
    rw [rationalDivisor_generator]
    simp [FiniteCorrespondenceGenerator.cycle]

@[simp] theorem generatorRationalFunction_primePolynomialGenerator
    (p : denominators R) (hp : Prime p.val) :
    generatorRationalFunction (primePolynomialGenerator (k := k) p.val p.property.1
      p.property.2 hp) = admissibleFraction p 1 := by
  apply Subtype.ext
  change fraction _ 1 = fraction p 1
  congr 1
  apply Subtype.ext
  exact coordinatePolynomial_primePolynomialGenerator p.val p.property.1 p.property.2 hp

/-- The recovery map is already an inverse on every monic prime polynomial. -/
theorem cycleRationalFunction_denominator_prime (p : denominators R) (hp : Prime p.val) :
    cycleRationalFunction (denominatorCycle (k := k) p) =
      Additive.ofMul (admissibleFraction p 1) := by
  change cycleRationalFunction (polynomialCycle p.val p.property.1 p.property.2) = _
  rw [polynomialCycle_eq_primeGenerator _ _ _ hp, cycleRationalFunction_cycle,
    generatorRationalFunction_primePolynomialGenerator]

/-- Product additivity extends the inverse identity to every finite prime factorization. -/
theorem cycleRationalFunction_denominator_prod (l : List (denominators R))
    (hl : ∀ p ∈ l, Prime p.val) :
    cycleRationalFunction (denominatorCycle (k := k) l.prod) =
      Additive.ofMul (admissibleFraction l.prod 1) := by
  induction l with
  | nil =>
    simp only [List.prod_nil, denominatorCycle_one, map_zero, admissibleFraction_self]
    rfl
  | cons p l ih =>
    have hp := hl p (by simp)
    have htail : ∀ q ∈ l, Prime q.val := fun q hq => hl q (by simp [hq])
    rw [List.prod_cons, denominatorCycle_mul, map_add,
      cycleRationalFunction_denominator_prime p hp, ih htail]
    change Additive.ofMul (admissibleFraction p 1 * admissibleFraction l.prod 1) = _
    rw [admissibleFraction_mul, one_mul]

include k in
omit [IsNoetherianRing R] in
/-- Normality supplies the finite admissible prime presentation of every denominator. -/
theorem exists_prime_denominator_factors (p : denominators R) :
    ∃ l : List (denominators R), l.prod = p ∧ ∀ q ∈ l, Prime q.val := by
  let : IsIntegrallyClosed R := isIntegrallyClosed_of_smooth_field k R
  obtain ⟨l, hl, hf⟩ := exists_list_monic_prime_factors_of_normal
    p.val p.property.1 p.property.2
  let l' : List (denominators R) := l.attach.map fun q =>
    ⟨q.val, (hf q.val q.property).1, (hf q.val q.property).2.2⟩
  refine ⟨l', ?_, ?_⟩
  · apply Subtype.ext
    change (denominators R).subtype l'.prod = p.val
    rw [map_list_prod]
    simpa [l', List.map_map] using hl
  · intro q hq
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hq
    exact (hf r.val r.property).2.1

/-- Every whole polynomial cycle recovers its literal monic equation. -/
@[simp] theorem cycleRationalFunction_denominator (p : denominators R) :
    cycleRationalFunction (denominatorCycle (k := k) p) =
      Additive.ofMul (admissibleFraction p 1) := by
  obtain ⟨l, rfl, hl⟩ := exists_prime_denominator_factors (k := k) p
  exact cycleRationalFunction_denominator_prod l hl

/-- The actual normalized rational function is recovered from its original divisor. -/
@[simp] theorem cycleRationalFunction_rationalDivisorHom
    (f : Additive (admissibleGroup R)) :
    cycleRationalFunction (k := k) (rationalDivisorHom f) = f := by
  obtain ⟨p, q, hf⟩ := f.toMul.property
  change cycleRationalFunction (rationalDivisor f.toMul) = f
  rw [rationalDivisor_eq _ _ _ hf, map_sub, cycleRationalFunction_denominator,
    cycleRationalFunction_denominator]
  apply congrArg Additive.ofMul
  apply Subtype.ext
  change fraction p 1 / fraction q 1 = f.toMul.val
  rw [hf]
  simp only [fraction, polynomialUnit_one, div_one]

/-- Actual normalized rational functions and the original correspondence group
are isomorphic on smooth integral affine sources. -/
def rationalDivisorEquiv : Additive (admissibleGroup R) ≃+
    FiniteCorrespondence (baseMap k R) (laurentProjection (.of k)) where
  toFun := rationalDivisorHom
  invFun := cycleRationalFunction
  left_inv := cycleRationalFunction_rationalDivisorHom
  right_inv := rationalDivisorHom_cycleRationalFunction
  map_add' := map_add rationalDivisorHom

/-- The boundary-one divisor map is injective for the actual original correspondences. -/
theorem boundaryDivisor_injective : Function.Injective (boundaryDivisor (k := k) (R := R)) := by
  intro f g h
  apply Additive.toMul.injective
  apply Subtype.ext
  have he := (rationalDivisorEquiv (k := k) (R := R)).injective h
  exact congrArg (fun x : Additive (admissibleGroup R) => x.toMul.val) he

end Motivic.AffineTorusPolynomialPresentation
