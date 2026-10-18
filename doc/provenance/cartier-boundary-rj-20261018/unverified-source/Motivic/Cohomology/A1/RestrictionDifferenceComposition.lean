/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.RelativeCurveLocalLifting
public import Motivic.AlgebraicGeometry.SmoothSiteNisnevichPullbacks

/-! # Composition of original signed restriction-difference lifts

An étale correction and a whole-zero open-neighborhood correction combine on
an actual common source. Their ambient terms are added after the specified
restrictions. The original section and both signs remain unchanged.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Motivic.PresheafWithTransfers

variable {k : Type u} [Field k] (P : PresheafWithTransfers.{u + 1} k)

/-- Two actual signed lifting identities compose along their original commuting maps.
The new ambient correction is the sum of the two restricted ambient corrections. -/
theorem HasRestrictionDifferenceLifting.comp
    {O₁ O₂ O T₁ T₂ T A₁ A₂ D : SmoothSite (Spec (.of k))}
    {φ₁ : O₁ ⟶ D} {β₁ : O₁ ⟶ A₁} {α₁ : O₁ ⟶ T₁}
    {φ₂ : O₂ ⟶ A₁} {β₂ : O₂ ⟶ A₂} {α₂ : O₂ ⟶ T₂}
    (h₁ : P.HasRestrictionDifferenceLifting φ₁ β₁ α₁)
    (h₂ : P.HasRestrictionDifferenceLifting φ₂ β₂ α₂)
    (f : O ⟶ O₁) (g : O ⟶ O₂) (hfg : f ≫ β₁ = g ≫ φ₂)
    (α : O ⟶ T) (c₁ : T ⟶ T₁) (c₂ : T ⟶ T₂)
    (hc₁ : α ≫ c₁ = f ≫ α₁) (hc₂ : α ≫ c₂ = g ≫ α₂) :
    P.HasRestrictionDifferenceLifting (f ≫ φ₁) (g ≫ β₂) α := by
  intro d
  let F := (toPresheaf k).obj P
  obtain ⟨b, c, hbc⟩ := h₁ d
  obtain ⟨a, e, hae⟩ := h₂ b
  refine ⟨a, F.map c₁.op c + F.map c₂.op e, ?_⟩
  have hbc' := congrArg (F.map f.op) hbc
  have hae' := congrArg (F.map g.op) hae
  have hfg' := ConcreteCategory.congr_hom (congrArg (fun q => F.map q.op) hfg) b
  have hc₁' := ConcreteCategory.congr_hom (congrArg (fun q => F.map q.op) hc₁) c
  have hc₂' := ConcreteCategory.congr_hom (congrArg (fun q => F.map q.op) hc₂) e
  simp only [map_sub] at hbc' hae'
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] at hfg' hc₁' hc₂'
  change F.map (g ≫ β₂).op a - F.map α.op (F.map c₁.op c + F.map c₂.op e) =
    F.map (f ≫ φ₁).op d
  rw [op_comp, op_comp, F.map_comp, F.map_comp, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, map_add, hc₁', hc₂']
  rw [show F.map g.op (F.map β₂.op a) -
      (F.map f.op (F.map α₁.op c) + F.map g.op (F.map α₂.op e)) =
      (F.map g.op (F.map β₂.op a) - F.map g.op (F.map α₂.op e)) -
        F.map f.op (F.map α₁.op c) by abel]
  rw [hae', ← hfg']
  exact hbc'

/-- For an actual étale square the common source and the new ambient correction
are constructed by native scheme pullbacks. Only the second square's original
commutativity is required; no refinement maps or lifting witnesses are assumed. -/
theorem HasRestrictionDifferenceLifting.comp_on_etale_pullback
    {O₁ O₂ T₁ T₂ A₁ A₂ B D : SmoothSite (Spec (.of k))}
    {φ₁ : O₁ ⟶ D} {β₁ : O₁ ⟶ A₁} {α₁ : O₁ ⟶ T₁}
    {φ₂ : O₂ ⟶ A₁} {β₂ : O₂ ⟶ A₂} {α₂ : O₂ ⟶ T₂}
    (h₁ : P.HasRestrictionDifferenceLifting φ₁ β₁ α₁)
    (h₂ : P.HasRestrictionDifferenceLifting φ₂ β₂ α₂)
    (a : A₁ ⟶ B) (p : T₁ ⟶ B) [Etale p.left]
    (H : IsPullback β₁ α₁ a p)
    (m : T₂ ⟶ B) (h : φ₂ ≫ a = α₂ ≫ m) :
    ∃ (f : SmoothSite.etalePullback p (φ₂ ≫ a) ⟶ O₁)
      (α : SmoothSite.etalePullback p (φ₂ ≫ a) ⟶ SmoothSite.etalePullback p m),
      f ≫ β₁ = SmoothSite.etalePullbackSnd p (φ₂ ≫ a) ≫ φ₂ ∧
      f ≫ α₁ = SmoothSite.etalePullbackFst p (φ₂ ≫ a) ∧
      α ≫ SmoothSite.etalePullbackFst p m = f ≫ α₁ ∧
      α ≫ SmoothSite.etalePullbackSnd p m =
        SmoothSite.etalePullbackSnd p (φ₂ ≫ a) ≫ α₂ ∧
      P.HasRestrictionDifferenceLifting (f ≫ φ₁)
        (SmoothSite.etalePullbackSnd p (φ₂ ≫ a) ≫ β₂) α := by
  let g := SmoothSite.etalePullbackSnd p (φ₂ ≫ a)
  let l := SmoothSite.etalePullbackFst p (φ₂ ≫ a)
  have hO : IsPullback l g p (φ₂ ≫ a) :=
    IsPullback.of_isLimit (SmoothSite.etalePullbackConeIsLimit p (φ₂ ≫ a))
  have hT : IsPullback (SmoothSite.etalePullbackFst p m)
      (SmoothSite.etalePullbackSnd p m) p m :=
    IsPullback.of_isLimit (SmoothSite.etalePullbackConeIsLimit p m)
  have hf : (g ≫ φ₂) ≫ a = l ≫ p :=
    (Category.assoc _ _ _).trans hO.w.symm
  have hα : l ≫ p = (g ≫ α₂) ≫ m := by
    exact hO.w.trans ((congrArg (fun f => g ≫ f) h).trans (Category.assoc _ _ _).symm)
  let f := H.lift (g ≫ φ₂) l hf
  let α := hT.lift l (g ≫ α₂) hα
  have hfg : f ≫ β₁ = g ≫ φ₂ := H.lift_fst _ _ _
  have hc₁ : α ≫ SmoothSite.etalePullbackFst p m = f ≫ α₁ :=
    (hT.lift_fst _ _ _).trans (H.lift_snd _ _ _).symm
  have hc₂ : α ≫ SmoothSite.etalePullbackSnd p m = g ≫ α₂ := hT.lift_snd _ _ _
  exact ⟨f, α, hfg, H.lift_snd _ _ _, hc₁, hc₂,
    HasRestrictionDifferenceLifting.comp P h₁ h₂ f g hfg α
      (SmoothSite.etalePullbackFst p m) (SmoothSite.etalePullbackSnd p m) hc₁ hc₂⟩

end Motivic.PresheafWithTransfers
