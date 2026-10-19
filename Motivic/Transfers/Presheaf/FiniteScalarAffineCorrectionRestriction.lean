/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.RestrictionDifferenceRefinement
public import Motivic.Transfers.Presheaf.FiniteSeparableExtension
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Pullbacks
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.BaseChange

/-! # Actual affine correction equations on the native scalar endpoint puncture

The endpoint source is the literal étale pullback over the scalar original
puncture. Its map to the produced correction puncture is constructed, and its
generator equation follows by cancellation of the original open immersion.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v u

namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  [Module.Finite k L] [Algebra.IsSeparable k L]

/-- Restrict a produced affine correction onto the exact scalar puncture used by
Weil descent. Both correction projections and the original generator are retained. -/
theorem restriction_difference_on_scalar_etale_pullback
    (P : PresheafWithTransfers.{v} k)
    {O₀ W₀ T₀ C₀ D A : SmoothSite (Spec (.of k))}
    (α₀ : O₀ ⟶ W₀) (β₀ : O₀ ⟶ T₀) (q₀ : W₀ ⟶ C₀) (j₀ : T₀ ⟶ C₀)
    (h₀ : β₀ ≫ j₀ = α₀ ≫ q₀)
    (φ₀ : O₀ ⟶ D) (δ : D ⟶ A) (e₀ : W₀ ⟶ A)
    (hφ₀ : φ₀ ≫ δ = α₀ ≫ e₀)
    [Mono ((SmoothSite.fieldBaseChange (algebraMap k L)).map δ)]
    {E' E O T C : SmoothSite (Spec (.of L))}
    (f : E' ⟶ (SmoothSite.fieldBaseChange (algebraMap k L)).obj W₀) [Etale f.left]
    (l : E' ⟶ E) (q : E ⟶ C) (j : T ⟶ C)
    (t : (SmoothSite.fieldBaseChange (algebraMap k L)).obj T₀ ⟶ T)
    (c : (SmoothSite.fieldBaseChange (algebraMap k L)).obj C₀ ⟶ C)
    (hlq : l ≫ q = f ≫ (SmoothSite.fieldBaseChange (algebraMap k L)).map q₀ ≫ c)
    (htj : t ≫ j = (SmoothSite.fieldBaseChange (algebraMap k L)).map j₀ ≫ c)
    (α : O ⟶ E) (β : O ⟶ T) (H : IsPullback β.left α.left j.left q.left)
    (η : E ⟶ (SmoothSite.fieldBaseChange (algebraMap k L)).obj A)
    (hlη : l ≫ η = f ≫ (SmoothSite.fieldBaseChange (algebraMap k L)).map e₀)
    (φ : O ⟶ (SmoothSite.fieldBaseChange (algebraMap k L)).obj D)
    (hφ : φ ≫ (SmoothSite.fieldBaseChange (algebraMap k L)).map δ = α ≫ η)
    (s : sections (finiteSeparableExtension L P)
      (Cor.mk ((SmoothSite.fieldBaseChange (algebraMap k L)).obj D)))
    (a : sections (finiteSeparableExtension L P) (Cor.mk T))
    (b : sections (finiteSeparableExtension L P) (Cor.mk E))
    (h : transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map β) a -
      transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map α) b =
        transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map φ) s) :
    let F := SmoothSite.fieldBaseChange (algebraMap k L)
    let αK := SmoothSite.etalePullbackFst f (F.map α₀)
    let βK := SmoothSite.etalePullbackSnd f (F.map α₀)
    transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map (βK ≫ F.map β₀))
        (transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map t) a) -
      transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map αK)
        (transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map l) b) =
      transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map (βK ≫ F.map φ₀)) s := by
  let F := SmoothSite.fieldBaseChange (algebraMap k L)
  let K := SmoothSite.etalePullback f (F.map α₀)
  let αK := SmoothSite.etalePullbackFst f (F.map α₀)
  let βK := SmoothSite.etalePullbackSnd f (F.map α₀)
  have hK : αK ≫ f = βK ≫ F.map α₀ :=
    (SmoothSite.etalePullbackCone f (F.map α₀)).condition
  have hc : (βK ≫ F.map β₀ ≫ t) ≫ j = (αK ≫ l) ≫ q := by
    calc
      _ = βK ≫ F.map β₀ ≫ F.map j₀ ≫ c := by rw [Category.assoc, Category.assoc, htj]
      _ = βK ≫ F.map α₀ ≫ F.map q₀ ≫ c := by
        rw [← Functor.map_comp_assoc, h₀, Functor.map_comp, Category.assoc]
      _ = (αK ≫ f) ≫ F.map q₀ ≫ c := by rw [← Category.assoc βK, ← hK]
      _ = (αK ≫ l) ≫ q := by rw [Category.assoc, Category.assoc, ← hlq]
  let γleft := H.lift (βK ≫ F.map β₀ ≫ t).left (αK ≫ l).left
    (congrArg (fun h => h.left) hc)
  have hγα : γleft ≫ α.left = (αK ≫ l).left := H.lift_snd _ _ _
  have hγβ : γleft ≫ β.left = (βK ≫ F.map β₀ ≫ t).left := H.lift_fst _ _ _
  let γ : K ⟶ O := SmoothSite.homMk γleft (by
    rw [← MorphismProperty.Over.w α, ← Category.assoc, hγα]
    exact MorphismProperty.Over.w (αK ≫ l))
  have hγα' : γ ≫ α = αK ≫ l := MorphismProperty.Over.Hom.ext hγα
  have hγβ' : γ ≫ β = (βK ≫ F.map β₀) ≫ t := by
    have hh : γ ≫ β = βK ≫ F.map β₀ ≫ t := MorphismProperty.Over.Hom.ext hγβ
    simpa only [Category.assoc] using hh
  have hγφ : γ ≫ φ = βK ≫ F.map φ₀ := by
    apply (cancel_mono (F.map δ)).mp
    calc
      _ = (γ ≫ α) ≫ η := by rw [Category.assoc, hφ, ← Category.assoc]
      _ = αK ≫ f ≫ F.map e₀ := by rw [hγα', Category.assoc, hlη]
      _ = βK ≫ F.map α₀ ≫ F.map e₀ := by rw [← Category.assoc αK, hK, Category.assoc]
      _ = (βK ≫ F.map φ₀) ≫ F.map δ := by
        rw [Category.assoc, ← Functor.map_comp, ← Functor.map_comp, hφ₀]
  exact restriction_difference_refinement (finiteSeparableExtension L P)
    (βK ≫ F.map β₀) αK (βK ≫ F.map φ₀) β α φ γ t l hγβ' hγα' hγφ s a b h

end Motivic.PresheafWithTransfers
