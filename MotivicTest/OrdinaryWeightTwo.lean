/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic
public import Mathlib.Algebra.Category.Grp.Abelian

/-!
# Integrated weight-two ordinary-presheaf coefficient construction

This consumer combines the genuine algebraic simplex over `Spec R`, singular
cochain placement in degree `2-r`, and the actual finite-coefficient cone.
It verifies the zero level-one theory and constructs the canonical level-six
Bockstein. The input is an ordinary abelian presheaf, so this is deliberately
not named motivic cohomology and does not bypass the missing transfer torus.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Motivic Motivic.AlgebraicSimplex Motivic.SingularComplex

universe u w

namespace Motivic.MotivicTest.OrdinaryWeightTwo

variable (R : Type u) [CommRing R]
variable (P : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ AddCommGrpCat.{w})

/-- An actual integer-indexed ordinary singular cochain complex on the relative simplex. -/
noncomputable def integral : CochainComplex AddCommGrpCat.{w} ℤ :=
  cochainObj (cosimplicialSchemeOver R) P 2

/-- An actual finite-coefficient complex, without supplying its groups as data. -/
noncomputable def finite (n : ℕ) : CochainComplex AddCommGrpCat.{w} ℤ :=
  finiteCoefficients (integral R P) n

/-- The full level-one complex has zero cohomology in every integer degree. -/
theorem level_one_zero (i : ℤ) : IsZero ((finite R P 1).homology i) :=
  finiteCoefficients.isZero_homology_one (integral R P) i

/-- The actual composite-level Bockstein has the required degree-one to degree-two type. -/
noncomputable def compositeBockstein :
    (finite R P 6).homology 1 ⟶ (integral R P).homology 2 :=
  finiteCoefficients.bocksteinHomology (integral R P) 6 1

/-- Every differential in the combined construction squares to zero. -/
theorem finite_d_squared (n : ℕ) (i j k : ℤ) :
    (finite R P n).d i j ≫ (finite R P n).d j k = 0 :=
  (finite R P n).d_comp_d i j k

end Motivic.MotivicTest.OrdinaryWeightTwo
