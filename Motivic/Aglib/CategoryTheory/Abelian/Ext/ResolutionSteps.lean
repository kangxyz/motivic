/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.CategoryTheory.Sites.SheafCohomology.Large.LocalTriviality

/-! # Ordinary Ext dimension shifting along explicit closed resolution steps

The intended consumer constructs each step from residue-field injective embeddings.
No vanishing or transfer-category injectivity is assumed by this lemma.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe w u v r
namespace CategoryTheory.Ext
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {A : Type r} (R : A → C) (P : C)

/-- Explicit injective steps with surjective ordinary Hom sections give all-degree
vanishing, with every quotient remaining in the same specified family. -/
theorem ext_eq_zero_of_resolution_steps
    (step : ∀ a, ∃ (a' : A) (I : C) (f : R a ⟶ I) (g : I ⟶ R a') (hfg : f ≫ g = 0),
      Injective I ∧ (ShortComplex.mk f g hfg).ShortExact ∧
        Function.Surjective (fun s : P ⟶ I => s ≫ g)) :
    ∀ (n : ℕ) (a : A) (e : Ext.{w} P (R a) (n + 1)), e = 0 := by
  intro n
  induction n with
  | zero =>
    intro a e
    obtain ⟨a', I, f, g, hfg, hI, hS, hs⟩ := step a
    have := hI
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ P hS e
      (Ext.eq_zero_of_injective _) rfl
    obtain ⟨t, ht⟩ := (Ext.mk₀_bijective P (R a')).surjective y
    obtain ⟨s, hs⟩ := hs t
    rw [← hy, ← ht, ← hs, ← Ext.mk₀_comp_mk₀]
    rw [Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]
  | succ n ih =>
    intro a e
    obtain ⟨a', I, f, g, hfg, hI, hS, _⟩ := step a
    have := hI
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ P hS e
      (Ext.eq_zero_of_injective _) rfl
    rw [← hy, ih a' y]
    exact Ext.zero_comp P (n + 1) hS.extClass _ rfl

end CategoryTheory.Ext
