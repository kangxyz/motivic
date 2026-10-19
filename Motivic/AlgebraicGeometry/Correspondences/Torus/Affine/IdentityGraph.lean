/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Torus.Affine.LinearGraph
public import Motivic.Aglib.RingTheory.Polynomial.BoundaryOneRationalFunctions.PointedExact

/-! # The genuine identity-point divisor and the original identity-axis graph -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent
open Polynomial.BoundaryOneRationalFunctions

universe u

namespace Motivic.AffineTorusPolynomialPresentation
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.SmoothSite

variable {k R : Type u} [Field k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]

/-- The actual affine structural morphism in the smooth site. -/
def affineStructureMorphism : affineSite k R ⟶ SmoothSite.base (Spec (.of k)) :=
  SmoothSite.homMk (baseMap k R) (Category.comp_id _)

/-- The literal unit-one morphism is the original base-point axis after the structure map. -/
theorem unitMorphism_one : unitMorphism (k := k) (1 : Rˣ) =
    affineStructureMorphism ≫ SmoothSite.torusOne (.of k) := by
  apply MorphismProperty.Over.Hom.ext
  change Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ (algebraMap k R) 1)) =
    Spec.map (CommRingCat.ofHom (algebraMap k R)) ≫
      Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ (RingHom.id k) 1))
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply CommRingCat.PolynomialLaurent.laurent_hom_ext
  · intro r
    change LaurentPolynomial.eval₂ (algebraMap k R) 1 (LaurentPolynomial.C r) =
      algebraMap k R (LaurentPolynomial.eval₂ (RingHom.id k) 1 (LaurentPolynomial.C r))
    simp
  · change LaurentPolynomial.eval₂ (algebraMap k R) 1 (LaurentPolynomial.T 1) =
      algebraMap k R (LaurentPolynomial.eval₂ (RingHom.id k) 1 (LaurentPolynomial.T 1))
    simp

variable [IsDomain R] [IsNoetherianRing R]

/-- The original rational function X - 1 has exactly the original identity graph as divisor. -/
theorem rationalDivisor_identityPoint_graph :
    rationalDivisor (k := k) (identityPointFraction (R := R)) =
      (Cor.graphFunctor k).map (unitMorphism (k := k) (1 : Rˣ)) := by
  rw [identityPointFraction, rationalDivisor_fraction, denominatorCycle_one, sub_zero]
  simpa only [denominatorCycle, linearDenominator, Units.val_neg, Units.val_one,
    sub_eq_add_neg, map_neg] using polynomialCycle_linear_graph (k := k) (1 : Rˣ)

/-- The graph's actual recovered function is the literal identity-point fraction. -/
@[simp] theorem cycleRationalFunction_identityGraph :
    cycleRationalFunction ((Cor.graphFunctor k).map (unitMorphism (k := k) (1 : Rˣ))) =
      Additive.ofMul (identityPointFraction (R := R)) := by
  rw [← rationalDivisor_identityPoint_graph]
  exact cycleRationalFunction_rationalDivisorHom (Additive.ofMul identityPointFraction)

/-- The actual signed-unit invariant kills the original identity graph. -/
@[simp] theorem signedValue_identityGraph :
    signedValueHom.toAdditive
      (cycleRationalFunction ((Cor.graphFunctor k).map (unitMorphism (k := k) (1 : Rˣ)))) = 0 := by
  rw [cycleRationalFunction_identityGraph]
  change Additive.ofMul (signedValueHom identityPointFraction) = 0
  rw [signedValueHom_identityPoint]
  rfl

end Motivic.AffineTorusPolynomialPresentation
