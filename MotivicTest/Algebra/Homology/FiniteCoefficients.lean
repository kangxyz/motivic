/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Motivic.Aglib.Algebra.Homology.CochainComplex.FiniteCoefficients.Module
import Motivic.Aglib.Algebra.Homology.CochainComplex.FiniteCoefficients.Cohomology

/-! # Coefficient regression tests

These tests check composite levels, signed representatives, the literal
Bockstein coordinate, arbitrary chain-map naturality, and level-one vanishing.
-/

open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open _root_.CochainComplex.finiteCoefficients

set_option backward.isDefEq.respectTransparency false
noncomputable section

universe u

variable (K L : CochainComplex (ModuleCat.{u} ℤ) ℤ)

/-- A composite-level cocycle uses `da = 6 b`, with the positive sign. -/
example (i : ℤ) (x : K.X i) (y : K.X (i + 1)) :
    (finiteCoefficients K 6).d i (i + 1) (ofPair K 6 i x y) = 0 ↔
      K.d i (i + 1) x = 6 • y ∧ K.d (i + 1) (i + 1 + 1) y = 0 := by
  rw [isCycle_iff]
  simp

/-- The connecting arrow really uses the positive second coordinate at level six. -/
example (i : ℤ) (x : K.X i) (y : K.X (i + 1)) :
    (bockstein K 6).f i (ofPair K 6 i x y) = y :=
  bockstein_ofPair K 6 i x y

/-- The constructed all-degree differential squares to zero on every pair. -/
example (n : ℕ) (i : ℤ) (x : K.X i) (y : K.X (i + 1)) :
    (finiteCoefficients K n).d (i + 1) (i + 1 + 1)
      ((finiteCoefficients K n).d i (i + 1) (ofPair K n i x y)) = 0 := by
  rw [← ModuleCat.comp_apply, HomologicalComplex.d_comp_d]
  simp

/-- Reduction from six to two multiplies the positive Bockstein coordinate by three. -/
example (i : ℤ) :
    (reduction K 2 3).f i ≫ b K 2 i = 3 • b K 6 i := by
  exact reduction_b K 2 3 i

/-- Insertion from two to six preserves the positive Bockstein coordinate. -/
example (i : ℤ) :
    (insertion K 2 3).f i ≫ b K 6 i = b K 2 i := by
  exact insertion_b K 2 3 i

/-- The two coefficient operations recover multiplication on the original complex. -/
example : insertion K 2 3 ≫ reduction K 2 3 = 3 • 𝟙 (finiteCoefficients K 2) :=
  insertion_reduction K 2 3

/-- Arbitrary maps of integral complexes commute with composite coefficient reduction. -/
example (f : K ⟶ L) :
    finiteCoefficients.map 6 f ≫ reduction L 2 3 =
      reduction K 2 3 ≫ finiteCoefficients.map 2 f :=
  reduction_naturality K 2 f 3

/-- Level one is contractible rather than an excluded coefficient level. -/
example : Homotopy (𝟙 (finiteCoefficients K 1)) 0 := contractionOne K

/-- Consequently, level one has zero cohomology in every integer degree. -/
example (i : ℤ) : IsZero ((finiteCoefficients K 1).homology i) :=
  isZero_homology_one K i

/-- The degree-one finite Bockstein has the actual integral degree-two target. -/
example : (finiteCoefficients K 6).homology 1 ⟶ K.homology 2 :=
  bocksteinHomology K 6 1
