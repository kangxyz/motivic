/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Pullbacks

/-! # Affine marked correction witnesses under an actual ambient restriction

The new witness is the actual pullback of the given étale witness along the
original ambient restriction. Whole sections are lifted without reducing their
source. A monomorphic base inclusion identifies its original cylinder map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

/-- Restrict an actual affine étale correction witness, retaining the original
ambient map and its whole marked section. The witness is constructed by pullback. -/
theorem exists_affine_marked_correction_restriction
    {k : Type u} [Field k]
    {E W W' C C' C'' : SmoothSite (Spec (.of k))}
    [IsAffine E.left] [IsAffine W.left] [IsAffine W'.left]
    (η : E ⟶ W) [Etale η.left] (r : W' ⟶ W)
    (q₀ : W ⟶ C) (q : E ⟶ C') (v : C' ⟶ C) [Mono v]
    (q' : W' ⟶ C'') [Etale q'.left] (u : C'' ⟶ C')
    (hbase : η ≫ q₀ = q ≫ v) (hr : r ≫ q₀ = q' ≫ u ≫ v)
    {Z : Scheme.{u}} (ζ : Z ⟶ E.left) (z' : Z ⟶ W'.left)
    (hmark : ζ ≫ η.left = z' ≫ r.left) :
    ∃ (E' : SmoothSite (Spec (.of k))) (l : E' ⟶ E) (n : E' ⟶ W')
      (ζ' : Z ⟶ E'.left),
      IsAffine E'.left ∧ Etale n.left ∧ Etale (n ≫ q').left ∧
      IsPullback l.left n.left η.left r.left ∧
      l ≫ η = n ≫ r ∧ l ≫ q = n ≫ q' ≫ u ∧
      ζ' ≫ l.left = ζ ∧ ζ' ≫ n.left = z' := by
  let E' := etalePullback η r
  let l := etalePullbackFst η r
  let n := etalePullbackSnd η r
  have hE : IsAffine E'.left := inferInstanceAs (IsAffine (pullback η.left r.left))
  have hn : Etale n.left := inferInstanceAs (Etale (pullback.snd η.left r.left))
  let := hn
  have hnq : Etale (n ≫ q').left := inferInstanceAs (Etale (n.left ≫ q'.left))
  have H : IsPullback l.left n.left η.left r.left :=
    IsPullback.of_hasPullback η.left r.left
  have hη : l ≫ η = n ≫ r := by
    apply MorphismProperty.Over.Hom.ext
    exact H.w
  have hq : l ≫ q = n ≫ q' ≫ u := by
    apply (cancel_mono v).mp
    calc
      (l ≫ q) ≫ v = l ≫ η ≫ q₀ := by rw [Category.assoc, ← hbase]
      _ = (n ≫ r) ≫ q₀ := by rw [← Category.assoc, hη]
      _ = (n ≫ q' ≫ u) ≫ v := by simp only [Category.assoc, hr]
  exact ⟨E', l, n, H.lift ζ z' hmark, hE, hn, hnq, H, hη, hq,
    H.lift_fst _ _ _, H.lift_snd _ _ _⟩

/-- The puncture of the restricted witness maps to the original Cartesian
puncture, with both actual projection equations. -/
theorem exists_correction_puncture_restriction
    {k : Type u} [Field k]
    {E E' C C' T T' O : SmoothSite (Spec (.of k))}
    (q : E ⟶ C) (q' : E' ⟶ C') [Etale q'.left]
    (l : E' ⟶ E) (u : C' ⟶ C) (hq : l ≫ q = q' ≫ u)
    (j : T ⟶ C) (j' : T' ⟶ C') (t : T' ⟶ T) (hj : t ≫ j = j' ≫ u)
    (α : O ⟶ E) (β : O ⟶ T) (H : IsPullback β.left α.left j.left q.left) :
    ∃ (O' : SmoothSite (Spec (.of k))) (α' : O' ⟶ E') (β' : O' ⟶ T')
      (γ : O' ⟶ O),
      IsPullback β'.left α'.left j'.left q'.left ∧
      γ ≫ α = α' ≫ l ∧ γ ≫ β = β' ≫ t := by
  let O' := etalePullback q' j'
  let α' := etalePullbackFst q' j'
  let β' := etalePullbackSnd q' j'
  have H' : IsPullback β'.left α'.left j'.left q'.left :=
    (IsPullback.of_hasPullback q'.left j'.left).flip
  have hsq : (β' ≫ t).left ≫ j.left = (α' ≫ l).left ≫ q.left := by
    have hq' : l.left ≫ q.left = q'.left ≫ u.left :=
      congrArg (fun f => f.left) hq
    have hj' : t.left ≫ j.left = j'.left ≫ u.left :=
      congrArg (fun f => f.left) hj
    change (β'.left ≫ t.left) ≫ j.left = (α'.left ≫ l.left) ≫ q.left
    rw [Category.assoc, hj', Category.assoc, hq', ← Category.assoc,
      H'.w, Category.assoc]
  let g := H.lift (β' ≫ t).left (α' ≫ l).left hsq
  have hgα : g ≫ α.left = (α' ≫ l).left := H.lift_snd _ _ _
  have hgβ : g ≫ β.left = (β' ≫ t).left := H.lift_fst _ _ _
  let γ : O' ⟶ O := homMk g (by
    rw [← MorphismProperty.Over.w α, ← Category.assoc, hgα]
    exact MorphismProperty.Over.w (α' ≫ l))
  refine ⟨O', α', β', γ, H', ?_, ?_⟩
  · apply MorphismProperty.Over.Hom.ext
    exact hgα
  · apply MorphismProperty.Over.Hom.ext
    exact hgβ

end AlgebraicGeometry.Scheme.SmoothSite
