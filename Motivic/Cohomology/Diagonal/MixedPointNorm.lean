/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Diagonal.CycleSymbols
public import Motivic.Cohomology.WeightOne.Equivalence
public import Motivic.Cohomology.WeightOne.FinitePointNorm

/-!
# All-weight fixed-coordinate norm relations

The whole finite polynomial interpolation survives literal target postcomposition
in every weight. Its identity-coordinate summands vanish in the original reduced
torus, giving the determinant norm formula for arbitrary signed unit-point cycles.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Polynomial

universe u

namespace Motivic.DiagonalMixedPointNorm
open _root_.AlgebraicGeometry.Scheme

open WeightOnePointNorm WeightOneBoundaryNorm WeightOneInterpolationCycle
open WeightOneSplitPolynomialCycle DiagonalCycleSymbols

variable (k : Type u) [Field k]

/-- The full monic interpolation relation survives any literal target graph. -/
theorem polynomial_postcompose (q : ℕ) (p : k[X]) (hp : p.Monic)
    (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0)
    (ψ : SmoothSite.torusPower (.of k) 1 ⟶ SmoothSite.torusPower (.of k) q) :
    cycleClass k q (polynomialCycle p hp h0 ≫ (Cor.graphFunctor k).map ψ) =
      cycleClass k q ((Cor.graphFunctor k).map
        (rationalPoint k (Units.mk0 (Polynomial.MonicUnitInterpolation.normValue p)
          (Polynomial.MonicUnitInterpolation.normValue_ne_zero p h0)) ≫ ψ)) +
        ((p.natDegree - 1 : ℕ) : ℤ) •
          cycleClass k q ((Cor.graphFunctor k).map (rationalPoint k 1 ≫ ψ)) := by
  let γ := (Cor.graphFunctor k).map ψ
  have h := cycleClass_endpoints k q (singularCorrespondence hp hd h0 ≫ γ)
  have hzero := congrArg (fun β => β ≫ γ) (singularCorrespondence_face_zero hp hd h0)
  have hone := congrArg (fun β => β ≫ γ) (singularCorrespondence_face_one hp hd h0)
  simp only [Category.assoc] at hzero hone h
  rw [hzero, hone, polynomialCycle_target p hd h0] at h
  simpa only [Preadditive.add_comp, Preadditive.zsmul_comp, map_add, map_zsmul,
    γ, ← Functor.map_comp] using h

private theorem generator_norm_polynomial (Z : WeightOnePointNorm.Generator k)
    (p : k[X]) (hp : p.Monic) (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0)
    (hZ : Z.cycle = polynomialCycle p hp h0) :
    generatorNorm Z = Units.mk0 (Polynomial.MonicUnitInterpolation.normValue p)
      (Polynomial.MonicUnitInterpolation.normValue_ne_zero p h0) := by
  have h := WeightOneEquivalence.cycleClass_polynomial k p hp hd h0
  rw [← hZ] at h
  have hn := congrArg (WeightOneHomologyNorm.homologyNorm k) h
  rw [WeightOneEquivalence.homologyNorm_cycleClass, cycleNorm_cycle,
    WeightOneHomologyNorm.homologyNorm_graphUnitClass] at hn
  exact congrArg Additive.toMul hn

/-- Full polynomial interpolation with arbitrary fixed coordinates. -/
theorem polynomial_varying (q : ℕ) (a : Fin q → kˣ) (i : Fin q)
    (p : k[X]) (hp : p.Monic) (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0) :
    cycleClass k q (polynomialCycle p hp h0 ≫
      (Cor.graphFunctor k).map (varyingCoordinate k q a i)) =
    graphSymbol k q (Function.update a i
      (Units.mk0 (Polynomial.MonicUnitInterpolation.normValue p)
        (Polynomial.MonicUnitInterpolation.normValue_ne_zero p h0))) := by
  have h := polynomial_postcompose k q p hp hd h0 (varyingCoordinate k q a i)
  simp only [rationalPoint_varyingCoordinate] at h
  change _ = graphSymbol k q _ + ((p.natDegree - 1 : ℕ) : ℤ) •
    graphSymbol k q (Function.update a i 1) at h
  simpa only [graphSymbol_one k q (Function.update a i 1) i
    (Function.update_self i 1 a), zsmul_zero, add_zero] using h

/-- Every original closed point retains its whole residue norm. -/
theorem generator_varying (q : ℕ) (a : Fin q → kˣ) (i : Fin q)
    (Z : WeightOnePointNorm.Generator k) :
    cycleClass k q (Z.cycle ≫ (Cor.graphFunctor k).map (varyingCoordinate k q a i)) =
      graphSymbol k q (Function.update a i (generatorNorm Z)) := by
  obtain ⟨p, hp, h0, hd, hZ⟩ := WeightOnePointPolynomial.exists_polynomialCycle Z
  rw [generator_norm_polynomial k Z p hp hd h0 hZ, hZ]
  exact polynomial_varying k q a i p hp hd h0

/-- The single varying slot is an additive map of units. -/
def varyingSymbol (q : ℕ) (a : Fin q → kˣ) (i : Fin q) :
    Additive kˣ →+ (motivicRawBaseComplex k q).homology q where
  toFun b := graphSymbol k q (Function.update a i b.toMul)
  map_zero' := graphSymbol_one k q (Function.update a i 1) i (Function.update_self i 1 a)
  map_add' b c := graphSymbol_mul k q a i b.toMul c.toMul

/-- Arbitrary signed finite cycles retain their full determinant norm. -/
theorem cycle_varying (q : ℕ) (a : Fin q → kˣ) (i : Fin q)
    (β : point k ⟶ WeightOnePointNorm.target k) :
    cycleClass k q (β ≫ (Cor.graphFunctor k).map (varyingCoordinate k q a i)) =
      graphSymbol k q (Function.update a i (cycleNorm k β).toMul) := by
  have h : (cycleClass k q).comp
      (Preadditive.rightComp (point k) ((Cor.graphFunctor k).map (varyingCoordinate k q a i))) =
      (varyingSymbol k q a i).comp (cycleNorm k) := by
    apply Finsupp.addHom_ext'
    intro Z
    apply AddMonoidHom.ext_int
    change cycleClass k q (Z.cycle ≫ (Cor.graphFunctor k).map (varyingCoordinate k q a i)) =
      graphSymbol k q (Function.update a i (cycleNorm k Z.cycle).toMul)
    rw [cycleNorm_cycle]
    exact generator_varying k q a i Z
  exact DFunLike.congr_fun h β

/-- The original finite point, including a proper-image residue degree, obeys the norm formula. -/
theorem finite_point_varying {E : Type u} [Field E] [Algebra k E] [Module.Finite k E]
    (q : ℕ) (a : Fin q → kˣ) (i : Fin q) (b : Eˣ) :
    cycleClass k q (WeightOneFinitePointNorm.unitPointCorrespondence (k := k) b ≫
      (Cor.graphFunctor k).map (varyingCoordinate k q a i)) =
        graphSymbol k q (Function.update a i (Units.map (Algebra.norm k) b)) := by
  rw [cycle_varying, WeightOneFinitePointNorm.cycleNorm_unitPointCorrespondence]
  rfl

end Motivic.DiagonalMixedPointNorm
