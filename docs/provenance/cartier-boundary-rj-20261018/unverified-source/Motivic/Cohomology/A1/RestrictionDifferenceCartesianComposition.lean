/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.RestrictionDifferenceComposition

/-! # The composed correction has its actual cartesian puncture

The same two ambient corrections used in the signed identity live on a genuine
base change of the first étale source. Its puncture is obtained by native
pullback cancellation and pasting, not supplied as another refinement premise.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.PresheafWithTransfers

/-- Composition preserves the actual puncture square of the second correction.
The original section, signs, both ambient maps and their native pullback are retained. -/
theorem HasRestrictionDifferenceLifting.comp_on_etale_pullback_cartesian
    {k : Type u} [Field k] (P : PresheafWithTransfers.{u + 1} k)
    {O₁ O₂ T₁ T₂ A₁ A₂ B C D : SmoothSite (Spec (.of k))}
    {φ₁ : O₁ ⟶ D} {β₁ : O₁ ⟶ A₁} {α₁ : O₁ ⟶ T₁}
    {φ₂ : O₂ ⟶ A₁} {β₂ : O₂ ⟶ A₂} {α₂ : O₂ ⟶ T₂}
    (h₁ : P.HasRestrictionDifferenceLifting φ₁ β₁ α₁)
    (h₂ : P.HasRestrictionDifferenceLifting φ₂ β₂ α₂)
    (a : A₁ ⟶ B) (p : T₁ ⟶ B) [Etale p.left]
    (H₁ : IsPullback β₁ α₁ a p)
    (m : T₂ ⟶ B) (h : φ₂ ≫ a = α₂ ≫ m)
    (j : A₂ ⟶ C) (q : T₂ ⟶ C) (H₂ : IsPullback β₂ α₂ j q) :
    ∃ (f : SmoothSite.etalePullback p (φ₂ ≫ a) ⟶ O₁)
      (α : SmoothSite.etalePullback p (φ₂ ≫ a) ⟶ SmoothSite.etalePullback p m),
      f ≫ β₁ = SmoothSite.etalePullbackSnd p (φ₂ ≫ a) ≫ φ₂ ∧
      f ≫ α₁ = SmoothSite.etalePullbackFst p (φ₂ ≫ a) ∧
      α ≫ SmoothSite.etalePullbackFst p m = f ≫ α₁ ∧
      α ≫ SmoothSite.etalePullbackSnd p m =
        SmoothSite.etalePullbackSnd p (φ₂ ≫ a) ≫ α₂ ∧
      IsPullback (SmoothSite.etalePullbackSnd p (φ₂ ≫ a) ≫ β₂) α j
        (SmoothSite.etalePullbackSnd p m ≫ q) ∧
      P.HasRestrictionDifferenceLifting (f ≫ φ₁)
        (SmoothSite.etalePullbackSnd p (φ₂ ≫ a) ≫ β₂) α := by
  obtain ⟨f, α, hfβ, hfα, hc₁, hc₂, hL⟩ :=
    HasRestrictionDifferenceLifting.comp_on_etale_pullback P h₁ h₂ a p H₁ m h
  refine ⟨f, α, hfβ, hfα, hc₁, hc₂, ?_, hL⟩
  have H₀ : IsPullback (SmoothSite.etalePullbackSnd p (φ₂ ≫ a))
      (α ≫ SmoothSite.etalePullbackFst p m) (α₂ ≫ m) p := by
    rw [hc₁, hfα, ← h]
    exact (IsPullback.of_isLimit
      (SmoothSite.etalePullbackConeIsLimit p (φ₂ ≫ a))).flip
  have HT : IsPullback (SmoothSite.etalePullbackSnd p m)
      (SmoothSite.etalePullbackFst p m) m p :=
    (IsPullback.of_isLimit (SmoothSite.etalePullbackConeIsLimit p m)).flip
  exact (H₀.of_bot hc₂.symm HT).paste_horiz H₂

end Motivic.PresheafWithTransfers
