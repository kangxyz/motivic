/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Torus.Affine.PolynomialBaseChange
public import Motivic.Aglib.RingTheory.Polynomial.BoundaryOneRationalFunctions.Invariants

/-! # Ordinary naturality of the genuine affine torus divisor equivalence -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent
open Polynomial.BoundaryOneRationalFunctions

universe u

namespace Motivic.AffineTorusPolynomialPresentation
open _root_.AlgebraicGeometry.PolynomialOpenQuotient.Laurent
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.SmoothSite

variable {k R S : Type u} [Field k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S] [Algebra.Smooth k R] [Algebra.Smooth k S]

/-- Ordinary restriction is precomposition by the original correspondence graph. -/
def affineRestriction (φ : R →ₐ[k] S) :
    FiniteCorrespondence (baseMap k R) (laurentProjection (.of k)) →+
      FiniteCorrespondence (baseMap k S) (laurentProjection (.of k)) :=
  Preadditive.leftComp (Cor.mk (SmoothSite.torus (.of k)))
    ((Cor.graphFunctor k).map (affineMorphism φ))

variable [IsDomain R] [IsDomain S] [IsNoetherianRing S]

/-- Original graph restriction of a basis generator keeps the whole mapped quotient. -/
theorem affineRestriction_generator (φ : R →ₐ[k] S) (Z : Generator k R) :
    affineRestriction φ Z.cycle =
      polynomialCycle (k := k) ((coordinatePolynomial Z).map φ.toRingHom)
        ((coordinatePolynomial_monic Z).map φ.toRingHom)
        (polynomialConstant_map_unit φ.toRingHom _ (coordinatePolynomial_constant_isUnit Z)) :=
  graph_generator_eq_polynomialCycle Z φ

/-- Rational recovery commutes with ordinary pullback on the original geometric basis. -/
theorem cycleRationalFunction_affineRestriction_generator
    (φ : R →ₐ[k] S) (Z : Generator k R) :
    cycleRationalFunction (affineRestriction φ Z.cycle) =
      (admissibleMap φ.toRingHom).toAdditive (cycleRationalFunction Z.cycle) := by
  rw [affineRestriction_generator, cycleRationalFunction_cycle]
  let p : denominators R := ⟨coordinatePolynomial Z, coordinatePolynomial_monic Z,
    coordinatePolynomial_constant_isUnit Z⟩
  change cycleRationalFunction (denominatorCycle (k := k) (denominatorMap φ.toRingHom p)) =
    Additive.ofMul (admissibleMap φ.toRingHom (admissibleFraction p 1))
  rw [cycleRationalFunction_denominator, admissibleMap_fraction, map_one]

/-- The actual recovered rational function is ordinary-natural for every algebra map,
including nonflat and noninjective maps. -/
theorem cycleRationalFunction_natural (φ : R →ₐ[k] S)
    (z : FiniteCorrespondence (baseMap k R) (laurentProjection (.of k))) :
    cycleRationalFunction (affineRestriction φ z) =
      (admissibleMap φ.toRingHom).toAdditive (cycleRationalFunction z) := by
  classical
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | single Z n =>
    have hs : Finsupp.single Z n = n • Z.cycle := by
      simp [FiniteCorrespondenceGenerator.cycle]
    rw [hs, map_zsmul, map_zsmul, map_zsmul, map_zsmul,
      cycleRationalFunction_affineRestriction_generator]

variable [IsNoetherianRing R]

/-- Divisors of actual rational fractions commute with original graph restriction. -/
theorem rationalDivisorHom_natural (φ : R →ₐ[k] S) (f : Additive (admissibleGroup R)) :
    affineRestriction φ (rationalDivisorHom f) =
      rationalDivisorHom ((admissibleMap φ.toRingHom).toAdditive f) := by
  apply (rationalDivisorEquiv (k := k) (R := S)).symm.injective
  change cycleRationalFunction (affineRestriction φ (rationalDivisorHom f)) =
    cycleRationalFunction (rationalDivisorHom ((admissibleMap φ.toRingHom).toAdditive f))
  rw [cycleRationalFunction_natural, cycleRationalFunction_rationalDivisorHom,
    cycleRationalFunction_rationalDivisorHom]

/-- The boundary-one subgroup maps to original correspondences by an ordinary-natural divisor. -/
theorem boundaryDivisor_natural (φ : R →ₐ[k] S) (f : Additive (group R)) :
    affineRestriction φ (boundaryDivisor f) =
      boundaryDivisor ((Polynomial.BoundaryOneRationalFunctions.map φ.toRingHom).toAdditive f) := by
  change affineRestriction φ (rationalDivisorHom (Additive.ofMul (boundaryInclusion f.toMul))) =
    rationalDivisorHom (Additive.ofMul
      (boundaryInclusion (Polynomial.BoundaryOneRationalFunctions.map φ.toRingHom f.toMul)))
  rw [rationalDivisorHom_natural]
  exact congrArg (fun g : admissibleGroup S => rationalDivisorHom (Additive.ofMul g))
    (boundaryInclusion_natural φ.toRingHom f.toMul)

/-- Whole polynomial cycles, not only prime factors, satisfy ordinary coefficient base change. -/
theorem polynomialCycle_natural (φ : R →ₐ[k] S) (p : R[X]) (hp : p.Monic)
    (h0 : IsUnit (p.coeff 0)) :
    affineRestriction φ (polynomialCycle (k := k) p hp h0) =
      polynomialCycle (k := k) (p.map φ.toRingHom) (hp.map φ.toRingHom)
        (polynomialConstant_map_unit φ.toRingHom p h0) := by
  let d : denominators R := ⟨p, hp, h0⟩
  have he := rationalDivisorHom_natural φ (Additive.ofMul (admissibleFraction d 1))
  change affineRestriction φ (rationalDivisor (admissibleFraction d 1)) =
    rationalDivisor (admissibleMap φ.toRingHom (admissibleFraction d 1)) at he
  simp only [admissibleMap_fraction, map_one, rationalDivisor_fraction,
    denominatorCycle_one, sub_zero] at he
  exact he

end Motivic.AffineTorusPolynomialPresentation
