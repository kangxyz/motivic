/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.OpenFiberShrinking

/-! # Retaining an original fiber isomorphism through actual open base restriction -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.Hom

/-- Restricting an original fiber isomorphism along a monic base map preserves it
whenever the original section over the unchanged specified fiber lifts through
the chosen open source. No reduction or pointwise substitute for the fiber is used. -/
theorem isIso_pullback_snd_of_open_source_of_mono_base
    {Y X Z Y' X' Z' : Scheme.{u}} (p : Y ⟶ X) (z : Z ⟶ X)
    [IsIso (pullback.snd p z)] (p' : Y' ⟶ X') (z' : Z' ⟶ X')
    (a : Y' ⟶ Y) [IsOpenImmersion a] (b : X' ⟶ X) [Mono b] (c : Z' ⟶ Z)
    (hp : p' ≫ b = a ≫ p) (hz : z' ≫ b = c ≫ z)
    (hretain : Set.range (c ≫ inv (pullback.snd p z) ≫ pullback.fst p z) ⊆ Set.range a) :
    IsIso (pullback.snd p' z') := by
  let s := inv (pullback.snd p z) ≫ pullback.fst p z
  have hsp : s ≫ p = z := by
    simp only [s, Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]
  let s' := IsOpenImmersion.lift a (c ≫ s) hretain
  have hsa : s' ≫ a = c ≫ s := IsOpenImmersion.lift_fac _ _ _
  have hsp' : s' ≫ p' = z' := by
    apply (cancel_mono b).mp
    rw [Category.assoc, hp, ← Category.assoc, hsa, Category.assoc, hsp]
    exact hz.symm
  let t : Z' ⟶ pullback p' z' := pullback.lift s' (𝟙 _) (by simpa using hsp')
  have ht : t ≫ pullback.snd p' z' = 𝟙 _ := pullback.lift_snd _ _ _
  let d : pullback p' z' ⟶ pullback p z :=
    pullback.lift (pullback.fst p' z' ≫ a) (pullback.snd p' z' ≫ c) (by
      rw [Category.assoc, ← hp, ← Category.assoc, pullback.condition,
        Category.assoc, hz, ← Category.assoc])
  have hfirst : (pullback.snd p' z' ≫ c) ≫ s = pullback.fst p' z' ≫ a := by
    calc
      _ = (d ≫ pullback.snd p z) ≫ s := by rw [pullback.lift_snd]
      _ = d ≫ pullback.fst p z := by simp [s]
      _ = _ := pullback.lift_fst _ _ _
  have hleft : pullback.snd p' z' ≫ t = 𝟙 _ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, t, pullback.lift_fst, Category.id_comp]
      apply (cancel_mono a).mp
      rw [Category.assoc, hsa, ← Category.assoc]
      exact hfirst
    · simp only [Category.assoc, ht, Category.comp_id, Category.id_comp]
  exact ⟨⟨t, hleft, ht⟩⟩

end AlgebraicGeometry.Scheme.Hom
