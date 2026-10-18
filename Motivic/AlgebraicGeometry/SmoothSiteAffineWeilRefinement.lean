/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.AffineWeilRestrictionNativePair
public import Motivic.AlgebraicGeometry.SmoothSiteBaseChange
public import Motivic.AlgebraicGeometry.SmoothSiteNisnevichPullbacks

/-! # Original smooth-site common affine refinements

The two evaluations are morphisms to the actual extended witnesses. The original
ambient and its whole mark are preserved, without assuming a common refinement.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module

universe u

namespace Motivic.SmoothSite

variable {k L₁ L₂ A T : Type u} [Field k] [Field L₁] [Field L₂]
variable [CommRing A] [CommRing T] [Algebra k L₁] [Algebra k L₂]
variable [Algebra k A] [Algebra A T]
variable {κ₁ κ₂ : Type u} [Finite κ₁] [Finite κ₂]
variable (b₁ : Basis κ₁ k L₁) (b₂ : Basis κ₂ k L₂)
variable {W V : SmoothSite (Spec (.of k))}
variable (z₀ : V ⟶ W) (e : Spec (.of A) ≅ W.left)
variable (he : e.hom ≫ W.hom = Spec.algebraMap k A)
variable (d : Spec (.of T) ≅ V.left)
variable (hmark : d.hom ≫ z₀.left = Spec.algebraMap A T ≫ e.hom)
variable {E₁ : SmoothSite (Spec (.of L₁))} {E₂ : SmoothSite (Spec (.of L₂))}
variable [IsAffine E₁.left] [IsAffine E₂.left]
variable (f₁ : E₁ ⟶ (fieldBaseChange (algebraMap k L₁)).obj W)
variable (f₂ : E₂ ⟶ (fieldBaseChange (algebraMap k L₂)).obj W)
variable [Etale f₁.left] [Etale f₂.left]
variable (t₁ : (fieldBaseChange (algebraMap k L₁)).obj V ⟶ E₁)
variable (t₂ : (fieldBaseChange (algebraMap k L₂)).obj V ⟶ E₂)
variable (ht₁ : t₁ ≫ f₁ = (fieldBaseChange (algebraMap k L₁)).map z₀)
variable (ht₂ : t₂ ≫ f₂ = (fieldBaseChange (algebraMap k L₂)).map z₀)

include b₁ b₂ e he d hmark ht₁ ht₂ in
/-- Actual finite-free scalar witnesses construct one original affine étale
smooth-site refinement and both marked native evaluations. -/
theorem exists_affine_etale_scalar_pair :
    ∃ (Y : SmoothSite (Spec (.of k))) (p : Y ⟶ W) (z : V ⟶ Y),
      z ≫ p = z₀ ∧ IsAffine Y.left ∧ Etale p.left ∧
      ∃ (a₁ : (fieldBaseChange (algebraMap k L₁)).obj Y ⟶ E₁)
        (a₂ : (fieldBaseChange (algebraMap k L₂)).obj Y ⟶ E₂),
        a₁ ≫ f₁ = (fieldBaseChange (algebraMap k L₁)).map p ∧
        a₂ ≫ f₂ = (fieldBaseChange (algebraMap k L₂)).map p ∧
        (fieldBaseChange (algebraMap k L₁)).map z ≫ a₁ = t₁ ∧
        (fieldBaseChange (algebraMap k L₂)).map z ≫ a₂ = t₂ := by
  have h₁ : t₁.left ≫ f₁.left = pullback.map V.hom (Spec.algebraMap k L₁)
      W.hom (Spec.algebraMap k L₁) z₀.left (𝟙 _) (𝟙 _)
      (by simp) (by simp) := by
    simpa [fieldBaseChange, baseChange_map_left, pullback.map] using
      congrArg (fun h => h.left) ht₁
  have h₂ : t₂.left ≫ f₂.left = pullback.map V.hom (Spec.algebraMap k L₂)
      W.hom (Spec.algebraMap k L₂) z₀.left (𝟙 _) (𝟙 _)
      (by simp) (by simp) := by
    simpa [fieldBaseChange, baseChange_map_left, pullback.map] using
      congrArg (fun h => h.left) ht₂
  have hpair := AffineWeilRestriction.exists_native_affine_etale_pair b₁ b₂ W.hom V.hom z₀.left
      (MorphismProperty.Over.w z₀).symm e he d hmark f₁.left f₂.left
      t₁.left t₂.left h₁ h₂
  rcases hpair with ⟨Y, p, z, hz, hY, hp, a₁, a₂, ha₁, ha₂, hm₁, hm₂⟩
  let := hY
  let := hp
  let Ys : SmoothSite (Spec (.of k)) := mk (p ≫ W.hom)
  let ps : Ys ⟶ W := homMk p rfl
  let zs : V ⟶ Ys := homMk z (by
    change z ≫ (p ≫ W.hom) = V.hom
    rw [← Category.assoc, hz, MorphismProperty.Over.w])
  have hbase₁ : a₁ ≫ E₁.hom = pullback.snd (p ≫ W.hom) (Spec.algebraMap k L₁) := by
    rw [← MorphismProperty.Over.w f₁, ← Category.assoc, ha₁]
    simp only [fieldBaseChange_obj_hom, pullback.map, pullback.lift_snd, Category.comp_id]
  have hbase₂ : a₂ ≫ E₂.hom = pullback.snd (p ≫ W.hom) (Spec.algebraMap k L₂) := by
    rw [← MorphismProperty.Over.w f₂, ← Category.assoc, ha₂]
    simp only [fieldBaseChange_obj_hom, pullback.map, pullback.lift_snd, Category.comp_id]
  refine ⟨Ys, ps, zs, ?_, hY, hp, homMk a₁ hbase₁, homMk a₂ hbase₂, ?_, ?_, ?_, ?_⟩
  · exact MorphismProperty.Over.Hom.ext hz
  · apply MorphismProperty.Over.Hom.ext
    simpa [Ys, ps, homMk, fieldBaseChange, baseChange_map_left, pullback.map] using ha₁
  · apply MorphismProperty.Over.Hom.ext
    simpa [Ys, ps, homMk, fieldBaseChange, baseChange_map_left, pullback.map] using ha₂
  · apply MorphismProperty.Over.Hom.ext
    simpa [Ys, zs, homMk, fieldBaseChange, baseChange_map_left, pullback.map] using hm₁
  · apply MorphismProperty.Over.Hom.ext
    simpa [Ys, zs, homMk, fieldBaseChange, baseChange_map_left, pullback.map] using hm₂

section Puncture

variable {S : Scheme.{u}} {Y W C U : SmoothSite S}
variable (p : Y ⟶ W) (q : W ⟶ C) (j : U ⟶ C)
variable [Etale p.left] [Etale q.left]

local instance etalePullbackRefinement_comp_etale : Etale (p ≫ q).left :=
  inferInstanceAs (Etale (p.left ≫ q.left))

/-- Restriction of the constructed ambient refinement to the direct puncture.
The source is the pullback over the original cylinder, not a scalar replacement. -/
def etalePullbackRefinement : etalePullback (p ≫ q) j ⟶ etalePullback q j :=
  (IsPullback.of_isLimit (etalePullbackConeIsLimit q j)).lift
    (etalePullbackFst (p ≫ q) j ≫ p) (etalePullbackSnd (p ≫ q) j) (by
      apply MorphismProperty.Over.Hom.ext
      exact (Category.assoc _ _ _).trans pullback.condition)

@[reassoc (attr := simp)]
theorem etalePullbackRefinement_fst :
    etalePullbackRefinement p q j ≫ etalePullbackFst q j =
      etalePullbackFst (p ≫ q) j ≫ p :=
  IsPullback.lift_fst _ _ _ _

@[reassoc (attr := simp)]
theorem etalePullbackRefinement_snd :
    etalePullbackRefinement p q j ≫ etalePullbackSnd q j =
      etalePullbackSnd (p ≫ q) j :=
  IsPullback.lift_snd _ _ _ _

end Puncture

end Motivic.SmoothSite
