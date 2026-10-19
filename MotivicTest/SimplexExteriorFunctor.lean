/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Exterior.Simplex.Functor

/-! # The actual additive simplex endofunctor on arbitrary signed correspondences -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Motivic

universe u

namespace MotivicTest.SimplexExteriorFunctor

variable {k : Type u} [Field k] {X Y Z : Cor k}

example (n : ℕ) : Cor k ⥤+ Cor k := Cor.simplexExteriorAdditiveFunctor k n

example (n : ℕ) :
    (Cor.simplexExteriorAdditiveFunctor k n).obj.map (𝟙 X) =
      𝟙 (Cor.simplexProduct X n) :=
  (Cor.simplexExteriorFunctor k n).map_id X

example (n : ℕ) (α : X ⟶ Y) (β : Y ⟶ Z) :
    (Cor.simplexExteriorAdditiveFunctor k n).obj.map (α ≫ β) =
      Cor.simplexExterior n α ≫ Cor.simplexExterior n β :=
  Cor.simplexExterior_comp n α β

example (n : ℕ) (α β : X ⟶ Y) :
    (Cor.simplexExteriorAdditiveFunctor k n).obj.map (α - β) =
      Cor.simplexExterior n α - Cor.simplexExterior n β :=
  (Cor.simplexExteriorFunctor k n).map_sub

end MotivicTest.SimplexExteriorFunctor
