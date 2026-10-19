/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Nisnevich.Lifting.FiniteFamilyLifting
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Pullbacks

/-!
# Arbitrary-family finite-support Nisnevich lifting in the smooth site

Over an affine base, an arbitrary separated étale family with actual
residue-field lifts on a finite fiber lifts a complete finite clopen partition
of the support after a pointed neighborhood in the smooth site. Restricting
the scheme-level neighborhood to an affine open preserves every branch map
and gives a smooth, separated, finite-type structure morphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme.SmoothSite

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Lift a finite clopen partition of the entire finite support through an
arbitrary separated étale family in the same smooth site. The index type may
be empty or infinite, and the support need not be reduced or flat. -/
theorem exists_nisnevich_family_lift_of_isFinite_with_point_property
    {S : Scheme.{u}} [IsAffine S] (X : SmoothSite S)
    {I : Type v} {Z : Scheme.{u}} (p : Z ⟶ X.left) [IsFinite p] (x : X.left)
    (V : I → Scheme.{u}) (q : ∀ i, V i ⟶ Z) (Q : ∀ i, V i → Prop)
    [∀ i, Etale (q i)] [∀ i, IsSeparated (q i)]
    (hq : ∀ z : Z, p z = x →
      ∃ (i : I) (v : V i), q i v = z ∧ IsIso ((q i).residueFieldMap v) ∧ Q i v) :
    ∃ (U : SmoothSite S) (g : U ⟶ X), Etale g.left ∧
    ∃ u : U.left, g.left u = x ∧ IsIso (g.left.residueFieldMap u) ∧
    ∃ (n : ℕ) (F : Fin n → (pullback p g.left).Opens),
      (∀ j, IsClopen (F j : Set (pullback p g.left : Scheme)) ∧
        IsFinite ((F j).ι ≫ pullback.snd p g.left)) ∧
      Pairwise (fun i j ↦ Disjoint (F i) (F j)) ∧ (⨆ j, F j) = ⊤ ∧
    ∃ (label : Fin n → I) (b : ∀ j, (F j).toScheme ⟶ V (label j)),
      ∀ j, b j ≫ q (label j) = (F j).ι ≫ pullback.fst p g.left ∧
        ∃ v : V (label j), Q (label j) v ∧
          ∀ t : (F j).toScheme, ((F j).ι ≫ pullback.snd p g.left) t = u → b j t = v := by
  obtain ⟨W, h, hh, w, hw, hr, n, E, hE, hEdisj, hEtop, label, b, hb⟩ :=
    AlgebraicGeometry.exists_nisnevich_family_lift_of_isFinite_with_point_property p x V q Q hq
  obtain ⟨u, hu⟩ := W.affineCover.covers w
  let j := W.affineCover.f (W.affineCover.idx w)
  let U : SmoothSite S := mk (j ≫ h ≫ X.hom)
  let g : U ⟶ X := homMk (j ≫ h) (by simp [U])
  let a : pullback p g.left ⟶ pullback p h :=
    pullback.map p g.left p h (𝟙 Z) j (𝟙 X.left) (by simp) (by simp [g])
  have ha : a ≫ pullback.fst p h = pullback.fst p g.left := by simp [a]
  have ha₂ : a ≫ pullback.snd p h = pullback.snd p g.left ≫ j := by simp [a]
  let F (i : Fin n) : (pullback p g.left).Opens := a ⁻¹ᵁ E i
  have hFclosed (i : Fin n) : IsClopen (F i : Set (pullback p g.left : Scheme)) :=
    (hE i).1.preimage a.continuous
  have hFfinite (i : Fin n) : IsFinite ((F i).ι ≫ pullback.snd p g.left) := by
    have : IsClosedImmersion (F i).ι := .of_isPreimmersion _ (by
      simpa only [Scheme.Opens.range_ι] using (hFclosed i).1)
    infer_instance
  have hFdisj : Pairwise (fun i k ↦ Disjoint (F i) (F k)) := by
    intro i k hik
    change Disjoint (a ⁻¹ᵁ E i) (a ⁻¹ᵁ E k)
    rw [disjoint_iff, ← Scheme.Hom.preimage_inf, disjoint_iff.mp (hEdisj hik),
      Scheme.Hom.preimage_bot]
  have hFtop : (⨆ i, F i) = ⊤ := a.iSup_preimage_eq_top hEtop
  have hlift (i : Fin n) :
      ∃ c : (F i).toScheme ⟶ V (label i),
        c ≫ q (label i) = (F i).ι ≫ pullback.fst p g.left ∧
        ∃ v : V (label i), Q (label i) v ∧
          ∀ z : (F i).toScheme, ((F i).ι ≫ pullback.snd p g.left) z = u → c z = v := by
    have hai : Set.range ((F i).ι ≫ a) ⊆ Set.range (E i).ι := by
      rintro z ⟨z', rfl⟩
      rw [Scheme.Opens.range_ι]
      exact z'.property
    let t : (F i).toScheme ⟶ (E i).toScheme :=
      IsOpenImmersion.lift (E i).ι ((F i).ι ≫ a) hai
    have ht : t ≫ (E i).ι = (F i).ι ≫ a :=
      IsOpenImmersion.lift_fac (E i).ι ((F i).ι ≫ a) hai
    obtain ⟨hbi, v, hvQ, hval⟩ := hb i
    refine ⟨t ≫ b i, ?_, v, hvQ, ?_⟩
    · rw [Category.assoc, hbi, ← Category.assoc, ht, Category.assoc, ha]
    · intro z hz
      apply hval (t z)
      have ht₂ : t ≫ (E i).ι ≫ pullback.snd p h =
          ((F i).ι ≫ pullback.snd p g.left) ≫ j := by
        rw [← Category.assoc, ht, Category.assoc, ha₂, ← Category.assoc]
      have he := congrArg (fun f : (F i).toScheme ⟶ W ↦ f z) ht₂
      change ((E i).ι ≫ pullback.snd p h) (t z) =
        j (((F i).ι ≫ pullback.snd p g.left) z) at he
      rw [hz, hu] at he
      exact he
  choose c hc using hlift
  refine ⟨U, g, ?_, u, ?_, ?_, n, F,
    fun i ↦ ⟨hFclosed i, hFfinite i⟩, hFdisj, hFtop, label, c, hc⟩
  · change Etale (j ≫ h)
    infer_instance
  · change h (j u) = x
    rw [hu, hw]
  · change IsIso ((j ≫ h).residueFieldMap u)
    rw [Scheme.residueFieldMap_comp]
    have : IsIso (h.residueFieldMap (j u)) := by rw [hu]; exact hr
    infer_instance

/-- The original smooth-site equality endpoint, from the same point-preserving
construction with no condition on the chosen residue-lift points. -/
theorem exists_nisnevich_family_lift_of_isFinite
    {S : Scheme.{u}} [IsAffine S] (X : SmoothSite S)
    {I : Type v} {Z : Scheme.{u}} (p : Z ⟶ X.left) [IsFinite p] (x : X.left)
    (V : I → Scheme.{u}) (q : ∀ i, V i ⟶ Z)
    [∀ i, Etale (q i)] [∀ i, IsSeparated (q i)]
    (hq : ∀ z : Z, p z = x →
      ∃ (i : I) (v : V i), q i v = z ∧ IsIso ((q i).residueFieldMap v)) :
    ∃ (U : SmoothSite S) (g : U ⟶ X), Etale g.left ∧
    ∃ u : U.left, g.left u = x ∧ IsIso (g.left.residueFieldMap u) ∧
    ∃ (n : ℕ) (F : Fin n → (pullback p g.left).Opens),
      (∀ j, IsClopen (F j : Set (pullback p g.left : Scheme)) ∧
        IsFinite ((F j).ι ≫ pullback.snd p g.left)) ∧
      Pairwise (fun i j ↦ Disjoint (F i) (F j)) ∧ (⨆ j, F j) = ⊤ ∧
    ∃ (label : Fin n → I) (b : ∀ j, (F j).toScheme ⟶ V (label j)),
      ∀ j, b j ≫ q (label j) = (F j).ι ≫ pullback.fst p g.left := by
  have hq' : ∀ z : Z, p z = x → ∃ (i : I) (v : V i),
      q i v = z ∧ IsIso ((q i).residueFieldMap v) ∧ True := by
    intro z hz
    obtain ⟨i, v, hv, hr⟩ := hq z hz
    exact ⟨i, v, hv, hr, trivial⟩
  obtain ⟨U, g, hg, u, hu, hr, n, F, hF, hd, ht, label, b, hb⟩ :=
    exists_nisnevich_family_lift_of_isFinite_with_point_property X p x V q
      (fun _ _ ↦ True) hq'
  exact ⟨U, g, hg, u, hu, hr, n, F, hF, hd, ht, label, b, fun j ↦ (hb j).1⟩

end AlgebraicGeometry.Scheme.SmoothSite
