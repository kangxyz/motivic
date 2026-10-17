/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.ExteriorIdentityComposition
public import Motivic.AlgebraicGeometry.Correspondences.ExteriorIdentityUnit
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# The actual additive simplex exterior endofunctor

The object is the literal relative product with the barycentric simplex. The map
is the signed exterior operation on genuine correspondence supports. Its identity
and composition equations are the proved actual cycle identities.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic.Cor

variable (k : Type u) [Field k]

/-- Adjoining the actual simplex is a functor on signed finite correspondences. -/
def simplexExteriorFunctor (n : ℕ) : Cor k ⥤ Cor k where
  obj X := simplexProduct X n
  map α := simplexExterior n α
  map_id X := simplexExterior_id n X
  map_comp α β := simplexExterior_comp n α β

@[simp] theorem simplexExteriorFunctor_obj (n : ℕ) (X : Cor k) :
    (simplexExteriorFunctor k n).obj X = simplexProduct X n := rfl

@[simp] theorem simplexExteriorFunctor_map (n : ℕ) {X Y : Cor k} (α : X ⟶ Y) :
    (simplexExteriorFunctor k n).map α = simplexExterior n α := rfl

instance simplexExteriorFunctor_additive (n : ℕ) : (simplexExteriorFunctor k n).Additive where
  map_add := map_add (simplexExterior n) _ _

/-- The public bundled additive endofunctor uses the actual exterior correspondence. -/
def simplexExteriorAdditiveFunctor (n : ℕ) : Cor k ⥤+ Cor k :=
  AdditiveFunctor.of (simplexExteriorFunctor k n)

@[simp] theorem simplexExteriorAdditiveFunctor_obj (n : ℕ) (X : Cor k) :
    (simplexExteriorAdditiveFunctor k n).obj.obj X = simplexProduct X n := rfl

@[simp] theorem simplexExteriorAdditiveFunctor_map (n : ℕ) {X Y : Cor k} (α : X ⟶ Y) :
    (simplexExteriorAdditiveFunctor k n).obj.map α = simplexExterior n α := rfl

end Motivic.Cor
