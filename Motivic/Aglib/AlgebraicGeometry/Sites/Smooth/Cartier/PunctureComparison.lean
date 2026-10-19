/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.Complement
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Pullbacks
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-! # Actual punctures in a common Cartier cylinder chart

Both complete closed-fiber squares determine the actual complementary open
square. Its source is the literal pullback of the original open complement;
the resulting map retains the specified base structures.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

private theorem range_fst_of_cartesian {D A B C : Scheme.{u}}
    {d : D ⟶ A} {e : D ⟶ B} {a : A ⟶ C} {i : B ⟶ C}
    (h : IsPullback d e a i) : Set.range d = a ⁻¹' Set.range i := by
  rw [← h.isoPullback_hom_fst]
  change Set.range ((pullback.fst a i) ∘ h.isoPullback.hom) = _
  rw [Set.range_comp, Set.range_eq_univ.mpr h.isoPullback.hom.surjective,
    Set.image_univ, Scheme.Pullback.range_fst]

/-- The original open pullback in a common full-fiber chart maps to the literal
Laurent cylinder, and both original puncture squares are Cartesian. -/
theorem exists_cartier_puncture_comparison (R : CommRingCat.{u})
    {U Y V D : SmoothSite (Spec R)} (j : U ⟶ Y) [IsOpenImmersion j.left]
    (a : V ⟶ Y) (b : V ⟶ a1Cylinder R D) (d : D ⟶ V)
    {Z : Scheme.{u}} (i : Z ⟶ Y.left) (e : D.left ⟶ Z)
    (hpa : IsPullback d.left e a.left i)
    (hpb : IsPullback d.left (𝟙 _) b.left (a1Section R D 0).left)
    (hcomp : Set.range i = (Set.range j.left)ᶜ) :
    IsPullback (etalePullbackFst j a) (etalePullbackSnd j a) j a ∧
      ∃ t : etalePullback j a ⟶ torusCylinder R D,
        IsPullback t (etalePullbackSnd j a) (contractionOpen R D) b := by
  let c := contractionOpen R D
  let W := etalePullback j a
  let w := etalePullbackSnd j a
  have : IsOpenImmersion w.left :=
    inferInstanceAs (IsOpenImmersion (pullback.snd j.left a.left))
  refine ⟨IsPullback.of_isLimit (etalePullbackConeIsLimit j a), ?_⟩
  have hr : Set.range w.left = b.left ⁻¹' Set.range c.left := by
    have hj : Set.range j.left = (Set.range i)ᶜ := by rw [hcomp, compl_compl]
    calc
      Set.range w.left = a.left ⁻¹' Set.range j.left :=
        Scheme.Pullback.range_snd j.left a.left
      _ = (Set.range d.left)ᶜ := by
        rw [hj, Set.preimage_compl, ← range_fst_of_cartesian hpa]
      _ = b.left ⁻¹' Set.range c.left := by
        rw [range_fst_of_cartesian hpb, range_a1Section_zero,
          Set.preimage_compl, compl_compl]
  have hlift : Set.range (w.left ≫ b.left) ⊆ Set.range c.left := by
    rintro _ ⟨x, rfl⟩
    exact (show w.left x ∈ b.left ⁻¹' Set.range c.left from hr ▸ ⟨x, rfl⟩)
  let t₀ := IsOpenImmersion.lift c.left (w.left ≫ b.left) hlift
  have ht₀ : t₀ ≫ c.left = w.left ≫ b.left := IsOpenImmersion.lift_fac _ _ _
  let t : W ⟶ torusCylinder R D := homMk t₀ (by
    rw [← MorphismProperty.Over.w c, ← Category.assoc, ht₀,
      Category.assoc, MorphismProperty.Over.w b, MorphismProperty.Over.w w])
  refine ⟨t, ?_⟩
  apply IsPullback.of_map_of_faithful (forgetScheme (Spec R))
  apply IsOpenImmersion.isPullback t₀ w.left c.left b.left ht₀.symm
  ext x
  change b.left x ∈ Set.range c.left ↔ x ∈ Set.range w.left
  exact (Set.ext_iff.mp hr x).symm

end AlgebraicGeometry.Scheme.SmoothSite
