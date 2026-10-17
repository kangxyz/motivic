/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.WeightTwoSymbols
public import Motivic.Cohomology.Motivic.WeightOneEquivalence
public import Motivic.Cohomology.Motivic.WeightOneFinitePointNorm

/-!
# Fixed-coordinate norm relations in actual weight-two homology

Postcomposition of the proved whole polynomial interpolation preserves its
actual endpoint boundary. An identity coordinate kills the extra split points.
Thus an arbitrary signed weight-one cycle, after adjoining a fixed coordinate,
has the weight-two symbol of its original norm. This is a relation inside the
existing raw homology, without assuming a corestriction map or Steinberg.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Polynomial

universe u

namespace Motivic.WeightTwoMixedNorm

open WeightOnePointNorm WeightOneBoundaryNorm WeightOneInterpolationCycle
open WeightOneSplitPolynomialCycle WeightTwoSymbols

variable (k : Type u) [Field k]

/-- The full monic interpolation relation survives any literal target graph. -/
theorem polynomial_postcompose (p : k[X]) (hp : p.Monic)
    (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0)
    (ψ : SmoothSite.torusPower (.of k) 1 ⟶ SmoothSite.torusPower (.of k) 2) :
    cycleClass k (polynomialCycle p hp h0 ≫ (Cor.graphFunctor k).map ψ) =
      cycleClass k ((Cor.graphFunctor k).map
        (rationalPoint k (Units.mk0 (Polynomial.MonicUnitInterpolation.normValue p)
          (Polynomial.MonicUnitInterpolation.normValue_ne_zero p h0)) ≫ ψ)) +
        ((p.natDegree - 1 : ℕ) : ℤ) •
          cycleClass k ((Cor.graphFunctor k).map (rationalPoint k 1 ≫ ψ)) := by
  let γ := (Cor.graphFunctor k).map ψ
  have h := cycleClass_endpoints k (singularCorrespondence hp hd h0 ≫ γ)
  have hzero := congrArg (fun β => β ≫ γ) (singularCorrespondence_face_zero hp hd h0)
  have hone := congrArg (fun β => β ≫ γ) (singularCorrespondence_face_one hp hd h0)
  simp only [Category.assoc] at hzero hone h
  rw [hzero, hone, polynomialCycle_target p hd h0] at h
  simpa only [Preadditive.add_comp, Preadditive.zsmul_comp, map_add, map_zsmul,
    γ, ← Functor.map_comp] using h

/-- Adjoining a fixed left coordinate removes exactly the identity-coordinate summands. -/
theorem polynomial_prepend (a : kˣ) (p : k[X]) (hp : p.Monic)
    (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0) :
    cycleClass k (polynomialCycle p hp h0 ≫ (Cor.graphFunctor k).map (prependUnit k a)) =
      graphSymbol k a (Units.mk0 (Polynomial.MonicUnitInterpolation.normValue p)
        (Polynomial.MonicUnitInterpolation.normValue_ne_zero p h0)) := by
  have h := polynomial_postcompose k p hp hd h0 (prependUnit k a)
  simp only [rationalPoint_prependUnit] at h
  change _ = graphSymbol k a _ + ((p.natDegree - 1 : ℕ) : ℤ) • graphSymbol k a 1 at h
  simpa only [graphSymbol_one_right, zsmul_zero, add_zero] using h

/-- Adjoining a fixed right coordinate gives the same whole-family calculation. -/
theorem polynomial_append (a : kˣ) (p : k[X]) (hp : p.Monic)
    (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0) :
    cycleClass k (polynomialCycle p hp h0 ≫ (Cor.graphFunctor k).map (appendUnit k a)) =
      graphSymbol k (Units.mk0 (Polynomial.MonicUnitInterpolation.normValue p)
        (Polynomial.MonicUnitInterpolation.normValue_ne_zero p h0)) a := by
  have h := polynomial_postcompose k p hp hd h0 (appendUnit k a)
  simp only [rationalPoint_appendUnit] at h
  change _ = graphSymbol k _ a + ((p.natDegree - 1 : ℕ) : ℤ) • graphSymbol k 1 a at h
  simpa only [graphSymbol_one_left, zsmul_zero, add_zero] using h

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

/-- The actual closed-point generator retains its original norm after prepending a unit. -/
theorem generator_prepend (a : kˣ) (Z : WeightOnePointNorm.Generator k) :
    cycleClass k (Z.cycle ≫ (Cor.graphFunctor k).map (prependUnit k a)) =
      graphSymbol k a (generatorNorm Z) := by
  obtain ⟨p, hp, h0, hd, hZ⟩ := WeightOnePointPolynomial.exists_polynomialCycle Z
  rw [generator_norm_polynomial k Z p hp hd h0 hZ, hZ]
  exact polynomial_prepend k a p hp hd h0

/-- The actual closed-point generator retains its original norm after appending a unit. -/
theorem generator_append (a : kˣ) (Z : WeightOnePointNorm.Generator k) :
    cycleClass k (Z.cycle ≫ (Cor.graphFunctor k).map (appendUnit k a)) =
      graphSymbol k (generatorNorm Z) a := by
  obtain ⟨p, hp, h0, hd, hZ⟩ := WeightOnePointPolynomial.exists_polynomialCycle Z
  rw [generator_norm_polynomial k Z p hp hd h0 hZ, hZ]
  exact polynomial_append k a p hp hd h0

/-- Arbitrary signed cycles satisfy the genuine fixed-left-coordinate norm formula. -/
theorem cycle_prepend (a : kˣ) (β : point k ⟶ WeightOnePointNorm.target k) :
    cycleClass k (β ≫ (Cor.graphFunctor k).map (prependUnit k a)) =
      graphSymbol k a (cycleNorm k β).toMul := by
  have h : (cycleClass k).comp
      (Preadditive.rightComp (point k) ((Cor.graphFunctor k).map (prependUnit k a))) =
      (graphSymbolRightHom k a).comp (cycleNorm k) := by
    apply Finsupp.addHom_ext'
    intro Z
    apply AddMonoidHom.ext_int
    change cycleClass k (Z.cycle ≫ (Cor.graphFunctor k).map (prependUnit k a)) =
      graphSymbol k a (cycleNorm k Z.cycle).toMul
    rw [cycleNorm_cycle]
    exact generator_prepend k a Z
  exact DFunLike.congr_fun h β

/-- Arbitrary signed cycles satisfy the genuine fixed-right-coordinate norm formula. -/
theorem cycle_append (a : kˣ) (β : point k ⟶ WeightOnePointNorm.target k) :
    cycleClass k (β ≫ (Cor.graphFunctor k).map (appendUnit k a)) =
      graphSymbol k (cycleNorm k β).toMul a := by
  let hleft : Additive kˣ →+ (motivicRawBaseComplex k 2).homology 2 :=
    (graphSymbolHom k).flip (Additive.ofMul a)
  have h : (cycleClass k).comp
      (Preadditive.rightComp (point k) ((Cor.graphFunctor k).map (appendUnit k a))) =
      hleft.comp (cycleNorm k) := by
    apply Finsupp.addHom_ext'
    intro Z
    apply AddMonoidHom.ext_int
    change cycleClass k (Z.cycle ≫ (Cor.graphFunctor k).map (appendUnit k a)) =
      graphSymbol k (cycleNorm k Z.cycle).toMul a
    rw [cycleNorm_cycle]
    exact generator_append k a Z
  exact DFunLike.congr_fun h β

/-- An arbitrary extension-field unit point gives the original determinant norm symbol. -/
theorem finite_point_prepend {E : Type u} [Field E] [Algebra k E] [Module.Finite k E]
    (a : kˣ) (b : Eˣ) :
    cycleClass k (WeightOneFinitePointNorm.unitPointCorrespondence (k := k) b ≫
      (Cor.graphFunctor k).map (prependUnit k a)) =
        graphSymbol k a (Units.map (Algebra.norm k) b) := by
  rw [cycle_prepend, WeightOneFinitePointNorm.cycleNorm_unitPointCorrespondence]
  rfl

/-- The corresponding fixed-right-coordinate formula retains the same full norm. -/
theorem finite_point_append {E : Type u} [Field E] [Algebra k E] [Module.Finite k E]
    (a : kˣ) (b : Eˣ) :
    cycleClass k (WeightOneFinitePointNorm.unitPointCorrespondence (k := k) b ≫
      (Cor.graphFunctor k).map (appendUnit k a)) =
        graphSymbol k (Units.map (Algebra.norm k) b) a := by
  rw [cycle_append, WeightOneFinitePointNorm.cycleNorm_unitPointCorrespondence]
  rfl

end Motivic.WeightTwoMixedNorm
