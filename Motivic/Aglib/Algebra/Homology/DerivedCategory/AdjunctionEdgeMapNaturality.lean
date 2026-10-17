/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.DerivedCategory.AdjunctionEdgeMap

/-! # Edge maps and a natural transformation of exact coefficient functors -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe w₀ w₁ w₂ v₀ v₁ v₂ u₀ u₁ u₂
namespace CategoryTheory.Adjunction
variable {C : Type u₀} {D : Type u₁} {E : Type u₂}
  [Category.{v₀} C] [Category.{v₁} D] [Category.{v₂} E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasExt.{w₀} C] [HasExt.{w₁} D] [HasExt.{w₂} E]
  {L : D ⥤ E} {R : E ⥤ D} [L.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L] (adj : L ⊣ R)
  {A : C ⥤ D} {B : C ⥤ E} [A.Additive] [B.Additive]
  [PreservesFiniteLimits A] [PreservesFiniteColimits A]
  [PreservesFiniteLimits B] [PreservesFiniteColimits B]

/-- The ordinary edge composed with an adjoint coefficient map respects the actual mate. -/
theorem extEdge_mapExactFunctor_mate (α : A ⟶ B ⋙ R) (β : A ⋙ L ⟶ B)
    (hβ : ∀ F, L.map (α.app F) ≫ adj.counit.app (B.obj F) = β.app F)
    {P F : C} (n : ℕ) (x : Ext P F n) :
    adj.extEdge n ((x.mapExactFunctor A).comp (Ext.mk₀ (α.app F)) (add_zero n)) =
      (Ext.mk₀ (β.app P)).comp (x.mapExactFunctor B) (zero_add n) := by
  simp only [extEdge, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  rw [Ext.comp_assoc _ _ _ _ (zero_add 0) (by omega), Ext.mk₀_comp_mk₀, hβ,
    ← Ext.comp_mapExactFunctor, Ext.mapExactFunctor_comp_mk₀_natTransApp]

/-- Source-compatible coefficient mates identify the original edge on every Ext class. -/
theorem extEdge_mapExactFunctor_source (α : A ⟶ B ⋙ R) (β : A ⋙ L ⟶ B)
    (hβ : ∀ F, L.map (α.app F) ≫ adj.counit.app (B.obj F) = β.app F)
    {P F : C} {Q : D} {Q' : E} (m : Q ⟶ A.obj P) (s : Q' ⟶ L.obj Q)
    (t : Q' ⟶ B.obj P) (hs : s ≫ L.map m ≫ β.app P = t)
    (n : ℕ) (x : Ext P F n) :
    (Ext.mk₀ s).comp
      (adj.extEdge n (((Ext.mk₀ m).comp (x.mapExactFunctor A) (zero_add n)).comp
        (Ext.mk₀ (α.app F)) (add_zero n))) (zero_add n) =
      (Ext.mk₀ t).comp (x.mapExactFunctor B) (zero_add n) := by
  rw [Ext.comp_assoc _ _ _ _ (add_zero n) (by omega), extEdge_naturality_left,
    extEdge_mapExactFunctor_mate adj α β hβ]
  rw [← Ext.comp_assoc _ _ _ (zero_add 0) (zero_add n) (by omega), Ext.mk₀_comp_mk₀]
  rw [← Ext.comp_assoc _ _ _ (zero_add 0) (zero_add n) (by omega), Ext.mk₀_comp_mk₀,
    Category.assoc, hs]

end CategoryTheory.Adjunction
