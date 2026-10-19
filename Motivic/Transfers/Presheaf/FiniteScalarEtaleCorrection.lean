/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.FiniteScalarRefinementDifference
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Pullbacks

/-! # Correction refinement through an actual extended etale puncture

The puncture evaluation is constructed by the universal property of the
concrete smooth-site etale pullback. Its three correction squares are proved,
not supplied as refinement hypotheses. The ambient evaluation remains the
actual geometric input, and the coefficient is unchanged.
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

local notation "B" => SmoothSite.fieldBaseChange (algebraMap k L)

/-- An actual ambient evaluation induces the puncture evaluation and all three
signed-correction squares by the concrete etale pullback universal property. -/
def FiniteSeparableRefinementCorrection.ofEtalePullback
    (P : PresheafWithTransfers.{v} k)
    {O Y T O₀ W D : SmoothSite (Spec (.of k))}
    (α : O ⟶ Y) (β : O ⟶ T) (γ : O ⟶ O₀)
    (α₀ : O₀ ⟶ W) (β₀ : O₀ ⟶ T) (φ₀ : O₀ ⟶ D) (p : Y ⟶ W)
    (hγα : γ ≫ α₀ = α ≫ p) (hγβ : γ ≫ β₀ = β)
    {E : SmoothSite (Spec (.of L))} (f : E ⟶ (B).obj W) [Etale f.left]
    (a : (B).obj Y ⟶ E) (ha : a ≫ f = (B).map p)
    (s : sections P (Cor.mk D))
    (t : sections (finiteSeparableExtension L P) (Cor.mk ((B).obj T)))
    (c : sections (finiteSeparableExtension L P) (Cor.mk E))
    (h : transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map
          (SmoothSite.etalePullbackSnd f ((B).map α₀) ≫ (B).map β₀)) t -
        transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map
          (SmoothSite.etalePullbackFst f ((B).map α₀))) c =
        transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map
          (SmoothSite.etalePullbackSnd f ((B).map α₀) ≫ (B).map φ₀))
          (transfer P ((Cor.graphFunctor k).map
            (SmoothSite.fieldBaseChangeForgetProjection (L := L) D)) s)) :
    FiniteSeparableRefinementCorrection P L β α (γ ≫ φ₀) s := by
  have he : ((B).map α ≫ a) ≫ f = (B).map γ ≫ (B).map α₀ := by
    rw [Category.assoc, ha, ← Functor.map_comp, ← hγα, Functor.map_comp]
  have H : IsPullback (SmoothSite.etalePullbackFst f ((B).map α₀))
      (SmoothSite.etalePullbackSnd f ((B).map α₀)) f ((B).map α₀) :=
    IsPullback.of_isLimit (SmoothSite.etalePullbackConeIsLimit f ((B).map α₀))
  let q := H.lift ((B).map α ≫ a) ((B).map γ) he
  have hq₁ : q ≫ SmoothSite.etalePullbackFst f ((B).map α₀) = (B).map α ≫ a :=
    H.lift_fst _ _ _
  have hq₂ : q ≫ SmoothSite.etalePullbackSnd f ((B).map α₀) = (B).map γ :=
    H.lift_snd _ _ _
  refine {
    puncture := SmoothSite.etalePullback f ((B).map α₀)
    laurent := (B).obj T
    ambient := E
    beta := SmoothSite.etalePullbackSnd f ((B).map α₀) ≫ (B).map β₀
    alpha := SmoothSite.etalePullbackFst f ((B).map α₀)
    generator := SmoothSite.etalePullbackSnd f ((B).map α₀) ≫ (B).map φ₀
    punctureMap := q
    laurentMap := 𝟙 _
    ambientMap := a
    beta_square := ?_
    alpha_square := hq₁
    generator_square := ?_
    laurentSection := t
    ambientSection := c
    relation := h }
  · rw [← Category.assoc, hq₂, ← Functor.map_comp, hγβ, Category.comp_id]
  · rw [← Category.assoc, hq₂, Functor.map_comp]

end Motivic.PresheafWithTransfers
