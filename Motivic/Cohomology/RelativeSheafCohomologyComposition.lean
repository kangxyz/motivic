/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.RelativeSheafCohomologyNaturality

/-! # Composition of the actual relative restriction maps -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
universe w t v u
namespace Motivic.SheafCohomology
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v t}]
  {U₀ X₀ U₁ X₁ U₂ X₂ : C}
  (j₀ : U₀ ⟶ X₀) (j₁ : U₁ ⟶ X₁) (j₂ : U₂ ⟶ X₂)
  (a : U₀ ⟶ U₁) (b : X₀ ⟶ X₁) (h : j₀ ≫ b = a ≫ j₁)
  (a' : U₁ ⟶ U₂) (b' : X₁ ⟶ X₂) (h' : j₁ ≫ b' = a' ≫ j₂)
  (h'' : j₀ ≫ (b ≫ b') = (a ≫ a') ≫ j₂)

/-- Composition is induced by composition of the original site maps. -/
theorem relativeSourceMap_comp :
    relativeSourceMap J j₀ j₁ a b h ≫ relativeSourceMap J j₁ j₂ a' b' h' =
      relativeSourceMap J j₀ j₂ (a ≫ a') (b ≫ b') h'' := by
  apply (cancel_epi (relativeSourceπ J j₀)).mp
  simp only [← Category.assoc, relativeSourceπ_naturality]
  simp only [Category.assoc, relativeSourceπ_naturality]
  rw [Functor.map_comp, Category.assoc]

variable [HasExt.{w} (Sheaf J AddCommGrpCat.{max v t})]

/-- Relative Ext restriction composes with its literal coefficient squares. -/
theorem relativeRestriction_comp (F : Sheaf J AddCommGrpCat.{max v t}) (n : ℕ)
    (r : relativeH J j₂ F n) :
    relativeRestriction J j₀ j₁ a b h F n
        (relativeRestriction J j₁ j₂ a' b' h' F n r) =
      relativeRestriction J j₀ j₂ (a ≫ a') (b ≫ b') h'' F n r := by
  change Ext (relativeSource J j₂) F n at r
  change (Ext.mk₀ _).comp ((Ext.mk₀ _).comp r (zero_add n)) (zero_add n) =
    (Ext.mk₀ _).comp r (zero_add n)
  rw [Ext.mk₀_comp_mk₀_assoc, relativeSourceMap_comp J j₀ j₁ j₂ a b h a' b' h' h'']

include h in
/-- Killing an actual boundary representative after a refinement kills the original
relative class whenever the composite restriction is an excision isomorphism. -/
theorem relative_eq_zero_of_boundary_refinement [Mono j₀] [Mono j₁]
    (F : Sheaf J AddCommGrpCat.{max v t}) (n : ℕ)
    [IsIso (relativeRestriction J j₀ j₂ (a ≫ a') (b ≫ b') h'' F (n + 1))]
    (r : relativeH J j₂ F (n + 1)) (f : H J F n U₁)
    (hf : relativeRestriction J j₁ j₂ a' b' h' F (n + 1) r =
      relativeBoundary J j₁ F n f)
    (hz : (presheaf J F n).map a.op f = 0) : r = 0 := by
  apply (ConcreteCategory.bijective_of_isIso
    (relativeRestriction J j₀ j₂ (a ≫ a') (b ≫ b') h'' F (n + 1))).injective
  rw [map_zero, ← relativeRestriction_comp J j₀ j₁ j₂ a b h a' b' h' h'',
    hf, relativeBoundary_restriction, hz, map_zero]

end Motivic.SheafCohomology
