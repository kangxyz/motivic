/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction

/-! # The actual Ext edge map for an exact left adjoint

The right adjoint is not assumed exact. The map is the original exact-functor
map followed by the original counit, so it is meaningful before any Leray theorem.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe w₁ w₂ v₁ v₂ u₁ u₂
namespace CategoryTheory.Adjunction
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] [HasExt.{w₁} C] [HasExt.{w₂} D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L] (adj : L ⊣ R)

/-- The genuine edge map; no exactness hypothesis on the right adjoint is needed. -/
def extEdge {P : C} {Y : D} (n : ℕ) : Ext P (R.obj Y) n →+ Ext (L.obj P) Y n where
  toFun x := (x.mapExactFunctor L).comp (Ext.mk₀ (adj.counit.app Y)) (add_zero n)
  map_zero' := by simp
  map_add' x y := by simp

@[simp]
theorem extEdge_mk₀ {P : C} {Y : D} (f : P ⟶ R.obj Y) :
    adj.extEdge 0 (Ext.mk₀ f) = Ext.mk₀ ((adj.homEquiv P Y).symm f) := by
  simp [extEdge, Adjunction.homEquiv_counit, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]

/-- Degree zero is precisely the original adjunction, not an assumed edge isomorphism. -/
theorem extEdge_zero_bijective (P : C) (Y : D) :
    Function.Bijective (adj.extEdge (P := P) (Y := Y) 0) := by
  have h : (fun f : P ⟶ R.obj Y => adj.extEdge 0 (Ext.mk₀ f)) =
      fun f => Ext.mk₀ ((adj.homEquiv P Y).symm f) := by
    funext f
    exact adj.extEdge_mk₀ f
  have hb := (Ext.mk₀_bijective (L.obj P) Y).comp (adj.homEquiv P Y).symm.bijective
  change Function.Bijective (fun f => Ext.mk₀ ((adj.homEquiv P Y).symm f)) at hb
  rw [← h] at hb
  exact (Function.Bijective.of_comp_iff _ (Ext.mk₀_bijective P (R.obj Y))).mp hb

/-- Actual contravariant source maps commute with the edge. -/
theorem extEdge_naturality_left {P Q : C} {Y : D} (f : P ⟶ Q) (n : ℕ)
    (x : Ext Q (R.obj Y) n) :
    adj.extEdge n ((Ext.mk₀ f).comp x (zero_add n)) =
      (Ext.mk₀ (L.map f)).comp (adj.extEdge n x) (zero_add n) := by
  simp only [extEdge, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀]
  exact Ext.comp_assoc _ _ _ _ _ (by omega)

/-- Actual coefficient maps commute with the edge. -/
theorem extEdge_naturality_right {P : C} {Y Z : D} (g : Y ⟶ Z) (n : ℕ)
    (x : Ext P (R.obj Y) n) :
    adj.extEdge n (x.comp (Ext.mk₀ (R.map g)) (add_zero n)) =
      (adj.extEdge n x).comp (Ext.mk₀ g) (add_zero n) := by
  simp only [extEdge, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀]
  rw [Ext.comp_assoc _ _ _ _ (zero_add 0) (by omega), Ext.mk₀_comp_mk₀,
    show L.map (R.map g) ≫ adj.counit.app Z = adj.counit.app Y ≫ g from
      adj.counit.naturality g, ← Ext.mk₀_comp_mk₀]
  exact (Ext.comp_assoc _ _ _ _ _ (by omega)).symm

/-- The edge after the actual unit is the original exact inverse-image map. -/
theorem extEdge_unit {P Y : C} (n : ℕ) (x : Ext P Y n) :
    adj.extEdge n (x.comp (Ext.mk₀ (adj.unit.app Y)) (add_zero n)) =
      x.mapExactFunctor L := by
  simp only [extEdge, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀]
  rw [Ext.comp_assoc _ _ _ _ (zero_add 0) (by omega), Ext.mk₀_comp_mk₀,
    adj.left_triangle_components]
  simp

end CategoryTheory.Adjunction
