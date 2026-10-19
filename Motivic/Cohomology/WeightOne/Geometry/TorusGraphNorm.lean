/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightOne.Geometry.ReducedTorusNorm

/-! # The genuine ordinary norm sends a unit graph to that same unit -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial Opposite
open Polynomial.BoundaryOneRationalFunctions
open _root_.AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
open _root_.AlgebraicSimplex
open _root_.Motivic.PresheafWithTransfers

universe u

namespace Polynomial.BoundaryOneRationalFunctions

variable {R : Type u} [CommRing R] [Nontrivial R]

/-- The genuine rational function X - u with its monic normalization. -/
def unitPointFraction (u : Rˣ) : admissibleGroup R :=
  admissibleFraction (linearDenominator (-u)) 1

@[simp] theorem fractionDegree_unitPoint (u : Rˣ) :
    fractionDegree (unitPointFraction u) = 1 := by simp [unitPointFraction]

/-- The sign in the boundary invariant is exactly the one which recovers the point u. -/
@[simp] theorem signedValueHom_unitPoint (u : Rˣ) :
    signedValueHom (unitPointFraction u) = u := by
  change (-1 : Rˣ) ^ fractionDegree (unitPointFraction u) *
    zeroValueHom (unitPointFraction u) = u
  have h : denominatorConstant (1 : denominators R) = 1 := by
    apply Units.ext
    simp
  simp [unitPointFraction, h]

end Polynomial.BoundaryOneRationalFunctions

namespace Motivic.AffineTorusPolynomialPresentation

variable {k R : Type u} [Field k] [CommRing R] [Algebra k R]
  [Algebra.Smooth k R] [IsDomain R] [IsNoetherianRing R]

/-- The actual divisor of X - u is the original graph of the unit section. -/
theorem rationalDivisor_unitPoint_graph (u : Rˣ) :
    rationalDivisor (k := k) (unitPointFraction u) =
      (Cor.graphFunctor k).map (unitMorphism (k := k) u) := by
  rw [unitPointFraction, rationalDivisor_fraction, denominatorCycle_one, sub_zero]
  simpa only [denominatorCycle, linearDenominator, Units.val_neg,
    sub_eq_add_neg, map_neg] using polynomialCycle_linear_graph (k := k) u

/-- The original unit graph recovers the literal normalized linear rational function. -/
theorem cycleRationalFunction_unitGraph (u : Rˣ) :
    cycleRationalFunction ((Cor.graphFunctor k).map (unitMorphism (k := k) u)) =
      Additive.ofMul (unitPointFraction u) := by
  rw [← rationalDivisor_unitPoint_graph]
  exact cycleRationalFunction_rationalDivisorHom (Additive.ofMul (unitPointFraction u))

/-- The signed-unit invariant of the actual graph is its original unit, not its inverse. -/
theorem signedValue_unitGraph (u : Rˣ) :
    signedValueHom.toAdditive
      (cycleRationalFunction ((Cor.graphFunctor k).map (unitMorphism (k := k) u))) =
        Additive.ofMul u := by
  rw [cycleRationalFunction_unitGraph]
  exact congrArg Additive.ofMul (signedValueHom_unitPoint u)

end Motivic.AffineTorusPolynomialPresentation

namespace Motivic.SmoothSiteTorusDivisor
open _root_.AlgebraicGeometry.Scheme

open _root_.AlgebraicGeometry.PolynomialOpenQuotient.Laurent
open _root_.AlgebraicGeometry.Scheme.PolynomialLaurent
open _root_.AlgebraicGeometry.Scheme.SmoothSite
open _root_.Motivic.AffineTorusPolynomialPresentation

variable {k : Type u} [Field k]
attribute [local instance] sectionsAlgebra

/-- The original unit section, expressed in canonical global-section coordinates. -/
def affineUnitMorphism (X : SmoothSite (Spec (.of k))) [IsAffine X.left]
    (u : (Γ(X.left, ⊤))ˣ) : X ⟶ torus (.of k) :=
  (affineIso X).inv ≫ unitMorphism (k := k) u

/-- Canonical normalization: the actual norm of the actual unit graph is the unit itself. -/
theorem affineNorm_unitGraph (X : SmoothSite (Spec (.of k)))
    [IsAffine X.left] [IsIntegral X.left] (u : (Γ(X.left, ⊤))ˣ) :
    affineNorm X ((Cor.graphFunctor k).map (affineUnitMorphism X u)) = Additive.ofMul u := by
  have hc : affineCycleCoordinates X
      ((Cor.graphFunctor k).map (affineUnitMorphism X u)) =
        (Cor.graphFunctor k).map (unitMorphism (k := k) u) := by
    let e := (Cor.graphFunctor k).mapIso (affineIso X)
    change e.hom ≫ (Cor.graphFunctor k).map ((affineIso X).inv ≫ unitMorphism u) = _
    rw [Functor.map_comp]
    exact e.hom_inv_id_assoc _
  exact (congrArg ((signedValueHom (R := Γ(X.left, ⊤))).toAdditive.comp
    (cycleRationalFunction (k := k))) hc).trans (signedValue_unitGraph (k := k) u)

/-- The same original unit section, with the project's first torus-power target. -/
def affinePowerOneUnitMorphism (X : SmoothSite (Spec (.of k))) [IsAffine X.left]
    (u : (Γ(X.left, ⊤))ˣ) : X ⟶ torusPower (.of k) 1 :=
  affineUnitMorphism X u ≫ (torusPowerOneIso (.of k)).inv

/-- Canonical normalization also retains the actual first torus-power isomorphism. -/
theorem affinePowerOneNorm_unitGraph (X : SmoothSite (Spec (.of k)))
    [IsAffine X.left] [IsIntegral X.left] (u : (Γ(X.left, ⊤))ˣ) :
    affinePowerOneNorm X ((Cor.graphFunctor k).map (affinePowerOneUnitMorphism X u)) =
      Additive.ofMul u := by
  have ht : affinePowerOneUnitMorphism X u ≫
      (torusPowerOneIso (.of k)).hom = affineUnitMorphism X u := by
    change (affineUnitMorphism X u ≫ (torusPowerOneIso (.of k)).inv) ≫
      (torusPowerOneIso (.of k)).hom = _
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hg := ((Cor.graphFunctor k).map_comp (affinePowerOneUnitMorphism X u)
    (torusPowerOneIso (.of k)).hom).symm.trans
      (congrArg (Cor.graphFunctor k).map ht)
  exact (congrArg (affineNorm X) hg).trans (affineNorm_unitGraph X u)

/-- The constructed map on the original reduced torus sends the class of a genuine unit graph
precisely to that unit. -/
theorem reducedNorm_unitGraph (X : SmoothSite (Spec (.of k)))
    [IsAffine X.left] [IsIntegral X.left] (u : (Γ(X.left, ⊤))ˣ) :
    reducedNorm.app (op X) ((toReducedTorus k 1).hom.app (op (Cor.mk X))
      (ULift.up ((Cor.graphFunctor k).map (affinePowerOneUnitMorphism X u)))) =
        ULift.up (Additive.ofMul u) :=
  (reducedNorm_affine_apply X _).trans (congrArg ULift.up (affinePowerOneNorm_unitGraph X u))

end Motivic.SmoothSiteTorusDivisor
