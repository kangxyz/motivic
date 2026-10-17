/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.ExteriorIdentityComposition

/-! # Signed exterior composition, actual simplices, and zero coefficients -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Motivic

universe u

namespace MotivicTest.ExteriorIdentityComposition

variable {k : Type u} [Field k] {X Y Z : Cor k}

example (n : ℕ) (α : X ⟶ Y) (β : Y ⟶ Z) :
    Cor.simplexExterior n (α ≫ β) =
      Cor.simplexExterior n α ≫ Cor.simplexExterior n β :=
  Cor.simplexExterior_comp n α β

example (n : ℕ) (α : X ⟶ Y) (β : Y ⟶ Z) (a b : ℤ) :
    Cor.simplexExterior n ((a • α) ≫ (b • β)) =
      (a • Cor.simplexExterior n α) ≫ (b • Cor.simplexExterior n β) := by
  rw [Cor.simplexExterior_comp, map_zsmul, map_zsmul]

example (n : ℕ) (α α' : X ⟶ Y) (β : Y ⟶ Z) :
    Cor.simplexExterior n ((α - α') ≫ β) =
      (Cor.simplexExterior n α - Cor.simplexExterior n α') ≫ Cor.simplexExterior n β := by
  rw [Cor.simplexExterior_comp, map_sub]

example (n : ℕ) (β : Y ⟶ Z) :
    Cor.simplexExterior n ((0 : X ⟶ Y) ≫ β) = 0 := by simp

end MotivicTest.ExteriorIdentityComposition
