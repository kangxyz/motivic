/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Polynomial.BoundaryOneRationalFunctions.Admissible

public import Motivic.AlgebraicGeometry.Correspondences.Torus.Affine.PolynomialProducts
public import Motivic.Aglib.RingTheory.Polynomial.BoundaryOneRationalFunctions.Basic

/-!
# Divisors of actual admissible affine rational functions

The source groups are subgroups of units of the actual polynomial localization.
The divisor values are the original finite correspondences with their original
multiplicities. Cross-multiplication proves independence of the presentation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent

universe u


namespace Motivic.AffineTorusPolynomialPresentation

open Polynomial.BoundaryOneRationalFunctions

variable {k R : Type u} [Field k] [CommRing R] [Algebra k R]
  [IsDomain R] [IsNoetherianRing R]

/-- The actual polynomial correspondence as a function of an admissible denominator. -/
def denominatorCycle (p : denominators R) :
    FiniteCorrespondence (baseMap k R) (laurentProjection (.of k)) :=
  polynomialCycle p.val p.property.1 p.property.2

@[simp] theorem denominatorCycle_one : denominatorCycle (k := k) (1 : denominators R) = 0 :=
  polynomialCycle_one

theorem denominatorCycle_mul (p q : denominators R) :
    denominatorCycle (k := k) (p * q) = denominatorCycle p + denominatorCycle q :=
  polynomialCycle_mul p.val q.val p.property.1 q.property.1 p.property.2 q.property.2

/-- Equality in the actual localized ring implies equality of original signed divisors. -/
theorem divisor_presentation_independent (p q r s : denominators R)
    (h : fraction p q = fraction r s) :
    denominatorCycle (k := k) p - denominatorCycle q =
      denominatorCycle r - denominatorCycle s := by
  have he := fraction_eq_iff p q r s |>.mp h
  have hc := congrArg (denominatorCycle (k := k))
    (show p * s = r * q from Subtype.ext he)
  rw [denominatorCycle_mul, denominatorCycle_mul] at hc
  exact sub_eq_sub_iff_add_eq_add.mpr hc

/-- An original divisor exists independently of every admissible presentation. -/
theorem exists_divisor (f : admissibleGroup R) :
    ∃ z : FiniteCorrespondence (baseMap k R) (laurentProjection (.of k)),
      ∀ p q : denominators R, f.val = fraction p q →
        z = denominatorCycle p - denominatorCycle q := by
  obtain ⟨p, q, hf⟩ := f.property
  refine ⟨denominatorCycle p - denominatorCycle q, ?_⟩
  intro r s h
  exact divisor_presentation_independent p q r s (hf.symm.trans h)

/-- The divisor of an actual rational function, in the original correspondence group. -/
def rationalDivisor (f : admissibleGroup R) :
    FiniteCorrespondence (baseMap k R) (laurentProjection (.of k)) :=
  (exists_divisor (k := k) f).choose

theorem rationalDivisor_eq (f : admissibleGroup R) (p q : denominators R)
    (h : f.val = fraction p q) :
    rationalDivisor (k := k) f = denominatorCycle p - denominatorCycle q :=
  (exists_divisor (k := k) f).choose_spec p q h

@[simp] theorem rationalDivisor_fraction (p q : denominators R) :
    rationalDivisor (k := k) (admissibleFraction p q) =
      denominatorCycle p - denominatorCycle q := rationalDivisor_eq _ p q rfl

@[simp] theorem rationalDivisor_one : rationalDivisor (k := k) (1 : admissibleGroup R) = 0 := by
  rw [rationalDivisor_eq _ 1 1 (fraction_self 1).symm, sub_self]

theorem rationalDivisor_mul (f g : admissibleGroup R) :
    rationalDivisor (k := k) (f * g) = rationalDivisor f + rationalDivisor g := by
  obtain ⟨p, q, hf⟩ := f.property
  obtain ⟨r, s, hg⟩ := g.property
  have hfg : (f * g).val = fraction (p * r) (q * s) := by
    change f.val * g.val = _
    rw [hf, hg, fraction_mul]
  rw [rationalDivisor_eq _ _ _ hfg, rationalDivisor_eq _ _ _ hf,
    rationalDivisor_eq _ _ _ hg, denominatorCycle_mul, denominatorCycle_mul]
  abel

/-- The divisor is an actual homomorphism, unlike the interpolation homotopy. -/
def rationalDivisorHom : Additive (admissibleGroup R) →+
    FiniteCorrespondence (baseMap k R) (laurentProjection (.of k)) where
  toFun f := rationalDivisor f.toMul
  map_zero' := rationalDivisor_one
  map_add' f g := rationalDivisor_mul f.toMul g.toMul

/-- The actual MVW boundary-one rational-function divisor map on the affine source. -/
def boundaryDivisor : Additive (group R) →+
    FiniteCorrespondence (baseMap k R) (laurentProjection (.of k)) :=
  rationalDivisorHom.comp boundaryInclusion.toAdditive

variable [Algebra.Smooth k R]

/-- The original generator's actual defining rational polynomial. -/
def generatorRationalFunction (Z : Generator k R) : admissibleGroup R :=
  admissibleFraction ⟨coordinatePolynomial Z, coordinatePolynomial_monic Z,
    coordinatePolynomial_constant_isUnit Z⟩ 1

@[simp] theorem rationalDivisor_generator (Z : Generator k R) :
    rationalDivisor (k := k) (generatorRationalFunction Z) = Z.cycle := by
  rw [generatorRationalFunction, rationalDivisor_fraction, denominatorCycle_one, sub_zero]
  exact (generator_cycle_eq_polynomialCycle Z).symm

/-- Every original finite correspondence is a divisor of an actual monic rational fraction. -/
theorem rationalDivisorHom_surjective :
    Function.Surjective (rationalDivisorHom (k := k) (R := R)) := by
  classical
  intro z
  induction z using Finsupp.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add a b ha hb =>
    obtain ⟨f, rfl⟩ := ha
    obtain ⟨g, rfl⟩ := hb
    exact ⟨f + g, map_add _ f g⟩
  | single Z n =>
    refine ⟨n • Additive.ofMul (generatorRationalFunction Z), ?_⟩
    rw [map_zsmul]
    change n • rationalDivisor (generatorRationalFunction Z) = _
    rw [rationalDivisor_generator]
    simp [FiniteCorrespondenceGenerator.cycle]

end Motivic.AffineTorusPolynomialPresentation
