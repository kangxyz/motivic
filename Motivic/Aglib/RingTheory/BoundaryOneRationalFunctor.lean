/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.BoundaryOneRationalHomotopy
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Category.Ring.Basic

/-!
# The functor of affine boundary-one rational functions

All commutative rings and all ring homomorphisms are included, including
noninjective specializations and the zero ring. Additive notation is only a
type synonym for the actual multiplicative subgroup of localized units.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

universe u

namespace Polynomial.BoundaryOneRationalFunctions

/-- The additive-valued functor of actual affine boundary-one rational functions. -/
def functor : CommRingCat.{u} ⥤ AddCommGrpCat.{u} where
  obj R := AddCommGrpCat.of (Additive (group R))
  map φ := AddCommGrpCat.ofHom (map φ.hom).toAdditive
  map_id R := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro f
    exact congrArg Additive.ofMul (map_id f.toMul)
  map_comp φ ψ := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro f
    exact congrArg Additive.ofMul (map_comp φ.hom ψ.hom f.toMul)

@[simp] theorem functor_map_apply {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (f : group R) : functor.map φ (Additive.ofMul f) = Additive.ofMul (map φ.hom f) := rfl

/-- The additive-zero face condition is the literal multiplicative-one condition. -/
theorem functor_map_eq_zero_iff {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (f : group R) : functor.map φ (Additive.ofMul f) = 0 ↔ map φ.hom f = 1 := Iff.rfl

end Polynomial.BoundaryOneRationalFunctions
