/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ClosedSubschemeOpenExtension
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Removing the off-diagonal in a common étale neighborhood

When both closed fibers of a common étale comparison are the same self-fiber
product, remove its off-diagonal. Both resulting maps are isomorphisms over
the entire original closed subscheme. No rational-point or reducedness
hypothesis is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- The diagonal is retained in both closed fibers simultaneously. The hypotheses
are literal Cartesian squares, not just equalities of supports. -/
theorem exists_common_etale_neighborhood_of_diagonal
    {Z B X Y W : Scheme.{u}} (r : Z ⟶ B) [Etale r]
    (p : W ⟶ X) (q : W ⟶ Y) [Etale p] [Etale q]
    (a : Z ⟶ X) [IsClosedImmersion a] (b : Z ⟶ Y)
    (i : pullback r r ⟶ W)
    (hp : IsPullback i (pullback.fst r r) p a)
    (hq : IsPullback i (pullback.snd r r) q b) :
    ∃ (U : W.Opens) (j : Z ⟶ U.toScheme),
      Etale (U.ι ≫ p) ∧ Etale (U.ι ≫ q) ∧
      IsPullback j (𝟙 Z) (U.ι ≫ p) a ∧
      IsPullback j (𝟙 Z) (U.ι ≫ q) b ∧
      IsIso (pullback.snd (U.ι ≫ p) a) ∧
      IsIso (pullback.snd (U.ι ≫ q) b) := by
  have : IsClosedImmersion i := MorphismProperty.of_isPullback hp.flip inferInstance
  obtain ⟨U, j, _, hj⟩ := exists_open_extension_isPullback (pullback.diagonal r) i
  have h₁ : IsPullback j (𝟙 Z) (U.ι ≫ p) a := by
    simpa only [pullback.diagonal_fst] using hj.paste_vert hp
  have h₂ : IsPullback j (𝟙 Z) (U.ι ≫ q) b := by
    simpa only [pullback.diagonal_snd] using hj.paste_vert hq
  refine ⟨U, j, inferInstance, inferInstance, h₁, h₂, ?_, ?_⟩
  · have he := h₁.isoPullback_hom_snd
    have : IsIso (h₁.isoPullback.hom ≫ pullback.snd (U.ι ≫ p) a) := by rw [he]; infer_instance
    exact IsIso.of_isIso_comp_left h₁.isoPullback.hom _
  · have he := h₂.isoPullback_hom_snd
    have : IsIso (h₂.isoPullback.hom ≫ pullback.snd (U.ι ≫ q) b) := by rw [he]; infer_instance
    exact IsIso.of_isIso_comp_left h₂.isoPullback.hom _

/-- Two étale charts with the same closed restriction admit a common étale
neighborhood inducing the identity on that entire closed subscheme. This is the
geometric off-diagonal removal step for an adapted smooth-divisor chart. -/
theorem exists_common_etale_neighborhood_of_cartesian_charts
    {Z B X Y A : Scheme.{u}} (r : Z ⟶ B) [Etale r]
    (f : X ⟶ A) (g : Y ⟶ A) [Etale f] [Etale g]
    (a : Z ⟶ X) [IsClosedImmersion a] (b : Z ⟶ Y) (c : B ⟶ A)
    (hX : IsPullback a r f c) (hY : IsPullback b r g c) :
    ∃ (U : (pullback f g).Opens) (j : Z ⟶ U.toScheme),
      Etale (U.ι ≫ pullback.fst f g) ∧ Etale (U.ι ≫ pullback.snd f g) ∧
      IsPullback j (𝟙 Z) (U.ι ≫ pullback.fst f g) a ∧
      IsPullback j (𝟙 Z) (U.ι ≫ pullback.snd f g) b ∧
      IsIso (pullback.snd (U.ι ≫ pullback.fst f g) a) ∧
      IsIso (pullback.snd (U.ι ≫ pullback.snd f g) b) := by
  let i : pullback r r ⟶ pullback f g :=
    pullback.lift (pullback.fst r r ≫ a) (pullback.snd r r ≫ b) (by
      simp only [Category.assoc, hX.w, hY.w]
      rw [← Category.assoc, pullback.condition, Category.assoc])
  have hi₁ : i ≫ pullback.fst f g = pullback.fst r r ≫ a := pullback.lift_fst _ _ _
  have hi₂ : i ≫ pullback.snd f g = pullback.snd r r ≫ b := pullback.lift_snd _ _ _
  have hp : IsPullback i (pullback.fst r r) (pullback.fst f g) a := by
    have h := (IsPullback.of_hasPullback r r).flip.paste_horiz hY
    have h' : IsPullback (i ≫ pullback.snd f g) (pullback.fst r r) g (a ≫ f) := by
      simpa only [hi₂, hX.w] using h
    exact h'.of_right hi₁ (IsPullback.of_hasPullback f g).flip
  have hq : IsPullback i (pullback.snd r r) (pullback.snd f g) b := by
    have h := (IsPullback.of_hasPullback r r).paste_horiz hX
    have h' : IsPullback (i ≫ pullback.fst f g) (pullback.snd r r) f (b ≫ g) := by
      simpa only [hi₁, hY.w] using h
    exact h'.of_right hi₂ (IsPullback.of_hasPullback f g)
  exact exists_common_etale_neighborhood_of_diagonal r
    (pullback.fst f g) (pullback.snd f g) a b i hp hq

end AlgebraicGeometry.Scheme
