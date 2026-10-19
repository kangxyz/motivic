/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Open shrinking retaining an actual base-change isomorphism -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- If an open in the source retains the complete inverse image of a morphism,
an original base-change isomorphism remains an isomorphism after that open
restriction. No reducedness, closedness, or residue-field assumption is needed. -/
theorem isIso_pullback_snd_of_open_retains_fiber
    {V X Z : Scheme.{u}} (p : V ⟶ X) (z : Z ⟶ X)
    [IsIso (pullback.snd p z)] (T : V.Opens)
    (hT : p ⁻¹' Set.range z ⊆ (T : Set V)) :
    IsIso (pullback.snd (T.ι ≫ p) z) := by
  let a : Z ⟶ V := inv (pullback.snd p z) ≫ pullback.fst p z
  have hap : a ≫ p = z := by
    simp only [a, Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]
  have haT : Set.range a ⊆ Set.range T.ι := by
    rintro _ ⟨v, rfl⟩
    rw [Opens.range_ι]
    apply hT
    exact ⟨v, (congrArg (fun f : Z ⟶ X => f v) hap).symm⟩
  let aT : Z ⟶ T.toScheme := IsOpenImmersion.lift T.ι a haT
  have ha : aT ≫ T.ι = a := IsOpenImmersion.lift_fac _ _ _
  let t : Z ⟶ pullback (T.ι ≫ p) z := pullback.lift aT (𝟙 Z) (by
    rw [← Category.assoc, ha, hap, Category.id_comp])
  have ht : t ≫ pullback.snd (T.ι ≫ p) z = 𝟙 Z := pullback.lift_snd _ _ _
  let b : pullback (T.ι ≫ p) z ⟶ pullback p z :=
    pullback.lift (pullback.fst (T.ι ≫ p) z ≫ T.ι)
      (pullback.snd (T.ι ≫ p) z) (by simpa only [Category.assoc] using
        (pullback.condition (f := T.ι ≫ p) (g := z)))
  have hfirst : pullback.snd (T.ι ≫ p) z ≫ a =
      pullback.fst (T.ι ≫ p) z ≫ T.ι := by
    calc
      _ = (b ≫ pullback.snd p z) ≫ a := by rw [pullback.lift_snd]
      _ = b ≫ pullback.fst p z := by simp [a]
      _ = _ := pullback.lift_fst _ _ _
  have hleft : pullback.snd (T.ι ≫ p) z ≫ t = 𝟙 _ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, t, pullback.lift_fst, Category.id_comp]
      apply (cancel_mono T.ι).mp
      rw [Category.assoc, ha]
      exact hfirst
    · simp only [Category.assoc, ht, Category.comp_id, Category.id_comp]
  exact ⟨⟨t, hleft, ht⟩⟩

end AlgebraicGeometry.Scheme.Hom
