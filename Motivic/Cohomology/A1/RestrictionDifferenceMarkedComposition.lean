/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.RestrictionDifferenceCartesianComposition

/-! # Composing signed corrections retains the whole original marking

The actual pullback assembly is independent of the presentation used to produce
its two correction identities. This keeps that assembly separate from the large
concrete projective-coordinate expressions, without supplying either correction.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.PresheafWithTransfers

/-- Two signed correction identities assemble on their actual etale pullback,
retaining the original ambient morphism, complete marking and cartesian puncture. -/
theorem HasRestrictionDifferenceLifting.comp_on_marked_etale_pullback
    {k : Type u} [Field k] (P : PresheafWithTransfers.{u + 1} k)
    {O₁ O₂ T₁ T₂ A₁ A₂ B C D Y L : SmoothSite (Spec (.of k))}
    {φ₁ : O₁ ⟶ D} {β₁ : O₁ ⟶ A₁} {α₁ : O₁ ⟶ T₁}
    {φ₂ : O₂ ⟶ A₁} {β₂ : O₂ ⟶ A₂} {α₂ : O₂ ⟶ T₂}
    (h₁ : P.HasRestrictionDifferenceLifting φ₁ β₁ α₁)
    (h₂ : P.HasRestrictionDifferenceLifting φ₂ β₂ α₂)
    (a : A₁ ⟶ B) (p₁ : T₁ ⟶ B) [Etale p₁.left]
    (H₁ : IsPullback β₁ α₁ a p₁)
    (m : T₂ ⟶ B) (hm : φ₂ ≫ a = α₂ ≫ m)
    (j : A₂ ⟶ C) (q₂ : T₂ ⟶ C) [Etale q₂.left]
    (H₂ : IsPullback β₂ α₂ j q₂)
    (p : Y ⟶ L) (η₁ : T₁ ⟶ Y) (b : B.left ⟶ L.left)
    (H₀ : IsPullback p₁.left η₁.left b p.left)
    {K : Scheme.{u}} (i : L.left ⟶ K) (v : C.left ⟶ K)
    (hbase : m.left ≫ b ≫ i = q₂.left ≫ v)
    (ρ : D ⟶ Y) (hρ : φ₁ ≫ ρ = α₁ ≫ η₁)
    {Z : Scheme.{u}} (ζ₂ : Z ⟶ T₂.left) (s : Z ⟶ Y.left) (z : Z ⟶ C.left)
    (hz : ζ₂ ≫ m.left ≫ b = s ≫ p.left) (hζ₂ : ζ₂ ≫ q₂.left = z) :
    ∃ (E : SmoothSite (Spec (.of k))) (η : E ⟶ Y) (q : E ⟶ C) (ζ : Z ⟶ E.left),
      Etale q.left ∧ η.left ≫ p.left ≫ i = q.left ≫ v ∧
      ζ ≫ q.left = z ∧ ζ ≫ η.left = s ∧
      ∃ (O : SmoothSite (Spec (.of k))) (α : O ⟶ E) (β : O ⟶ A₂) (φ : O ⟶ D),
        IsPullback β.left α.left j.left q.left ∧
        φ ≫ ρ = α ≫ η ∧ P.HasRestrictionDifferenceLifting φ β α := by
  obtain ⟨g, α, _hgβ, _hgα, hαfst, _hαsnd, H, hL⟩ :=
    HasRestrictionDifferenceLifting.comp_on_etale_pullback_cartesian
      P h₁ h₂ a p₁ H₁ m hm j q₂ H₂
  let E := SmoothSite.etalePullback p₁ m
  let O := SmoothSite.etalePullback p₁ (φ₂ ≫ a)
  let l := SmoothSite.etalePullbackFst p₁ m
  let n := SmoothSite.etalePullbackSnd p₁ m
  let η : E ⟶ Y := l ≫ η₁
  let q : E ⟶ C := n ≫ q₂
  let β : O ⟶ A₂ := SmoothSite.etalePullbackSnd p₁ (φ₂ ≫ a) ≫ β₂
  let φ := g ≫ φ₁
  let : Etale n.left := by
    change Etale (pullback.snd p₁.left m.left)
    infer_instance
  have hq : Etale q.left := by
    change Etale (n.left ≫ q₂.left)
    infer_instance
  have HE : IsPullback n.left η.left (m.left ≫ b) p.left :=
    (IsPullback.of_hasPullback p₁.left m.left).flip.paste_vert H₀
  let ζ := HE.lift ζ₂ s hz
  have hζn : ζ ≫ n.left = ζ₂ := HE.lift_fst _ _ _
  have hζq : ζ ≫ q.left = z := by
    change ζ ≫ (n.left ≫ q₂.left) = z
    rw [← Category.assoc, hζn, hζ₂]
  refine ⟨E, η, q, ζ, hq, ?_, hζq, HE.lift_snd _ _ _, O, α, β, φ, ?_, ?_, hL⟩
  · calc
      _ = n.left ≫ m.left ≫ b ≫ i := by
        simpa only [Category.assoc] using congrArg (fun f => f ≫ i) HE.w.symm
      _ = q.left ≫ v := by rw [hbase]; rfl
  · let : Etale q.left := hq
    have Hq : IsPullback β α j q := H
    exact ((SmoothSite.forgetScheme (Spec (.of k))).map_isPullback Hq.flip).flip
  · change (g ≫ φ₁) ≫ ρ = α ≫ (l ≫ η₁)
    rw [Category.assoc, hρ, ← Category.assoc, ← hαfst, Category.assoc]

end Motivic.PresheafWithTransfers
