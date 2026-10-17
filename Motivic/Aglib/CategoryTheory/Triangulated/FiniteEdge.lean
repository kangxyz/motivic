/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Triangulated.TStructure.Basic

/-!
# Finite-degree edge maps from a specified distinguished triangle

These are the two finite-degree Hom consequences needed by a Leray edge argument.
The map is postcomposition with the original first triangle arrow. Constructing
that triangle from a genuine direct-image resolution, and proving its third
object has the stated bound, remain separate obligations.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Pretriangulated CategoryTheory.Limits

universe u v

namespace CategoryTheory.Triangulated.TStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  (t : TStructure C) (T : Triangle C) (hT : T ∈ distTriang C)
  (P : C) (n : ℤ) [t.IsLE P n]

include hT

/-- A cone starting in degree `n` gives injectivity at degree `n`.
No vanishing in degree `n` itself is required. -/
theorem postcomp_injective_of_cone_isGE [t.IsGE T.obj₃ n] :
    Function.Injective (fun f : P ⟶ T.obj₁ => f ≫ T.mor₁) := by
  intro f g hfg
  change f ≫ T.mor₁ = g ≫ T.mor₁ at hfg
  have hz : (f - g) ≫ T.mor₁ = 0 := by
    rw [Preadditive.sub_comp, hfg, sub_self]
  obtain ⟨a, ha⟩ := T.invRotate.coyoneda_exact₂ (inv_rot_of_distTriang _ hT) (f - g) hz
  have : t.IsGE T.invRotate.obj₁ (n + 1) := by
    change t.IsGE (T.obj₃⟦(-1 : ℤ)⟧) (n + 1)
    exact t.isGE_shift T.obj₃ n (-1) (n + 1) (by omega)
  have ha0 : a = 0 := t.zero a n (n + 1) (by omega)
  have : f - g = 0 := by
    rw [ha, ha0, zero_comp]
    rfl
  exact sub_eq_zero.mp this

/-- One additional degree of cone vanishing gives surjectivity at degree `n`. -/
theorem postcomp_surjective_of_cone_isGE [t.IsGE T.obj₃ (n + 1)] :
    Function.Surjective (fun f : P ⟶ T.obj₁ => f ≫ T.mor₁) := by
  intro f
  have hf : f ≫ T.mor₂ = 0 := t.zero (f ≫ T.mor₂) n (n + 1) (by omega)
  obtain ⟨g, hg⟩ := T.coyoneda_exact₂ hT f hf
  exact ⟨g, hg.symm⟩

/-- The original edge map is bijective when its cone starts above degree `n`. -/
theorem postcomp_bijective_of_cone_isGE [t.IsGE T.obj₃ (n + 1)] :
    Function.Bijective (fun f : P ⟶ T.obj₁ => f ≫ T.mor₁) := by
  have : t.IsGE T.obj₃ n := t.isGE_of_ge T.obj₃ n (n + 1) (by omega)
  exact ⟨t.postcomp_injective_of_cone_isGE T hT P n,
    t.postcomp_surjective_of_cone_isGE T hT P n⟩

end CategoryTheory.Triangulated.TStructure
