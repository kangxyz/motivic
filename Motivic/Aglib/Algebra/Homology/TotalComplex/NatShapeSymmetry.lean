/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.BifunctorFlip

/-! # Extracted ordinary primitive with the original parameters and maps -/

@[expose] public section
open CategoryTheory CategoryTheory.MonoidalCategory HomologicalComplex
universe u
namespace ComplexShape
/-- The standard nonnegative total differential has the Koszul symmetry sign. -/
instance chainNatTotalComplexShapeSymmetry :
    TotalComplexShapeSymmetry (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) where
  symm p q := Nat.add_comm q p
  σ p q := (-1 : ℤˣ) ^ (p * q)
  σ_ε₁ := by
    rintro _ p rfl q
    dsimp
    rw [mul_one, Nat.add_mul, one_mul, pow_add, mul_comm]
  σ_ε₂ := by
    rintro p _ q rfl
    dsimp
    rw [Nat.mul_add, Nat.mul_one, pow_add, mul_assoc, Int.units_mul_self,
      mul_one, one_mul]

end ComplexShape
