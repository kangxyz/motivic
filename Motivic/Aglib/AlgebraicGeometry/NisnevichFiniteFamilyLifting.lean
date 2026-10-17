/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.NisnevichFiniteLifting

/-!
# Nisnevich lifting through an arbitrary étale family

An arbitrary separated étale family with residue-field-isomorphism lifts over
one finite fiber lifts a finite clopen partition of the entire support after
a pointed Nisnevich base change. Each piece retains its own target and map;
there is no finiteness assumption on the family or auxiliary coproduct.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A finite support lifts through finitely many members of an arbitrary
separated étale family after a genuine pointed Nisnevich base change. The
chosen pieces are actual, pairwise disjoint clopen subschemes covering the
whole canonical pullback, and are finite over the neighborhood. The labels
need not be distinct. Empty fibers are included, without requiring a chosen
target, and no reducedness, flatness, or separability hypothesis is imposed. -/
theorem exists_nisnevich_family_lift_of_isFinite_with_point_property
    {I : Type v} {Z S : Scheme.{u}} (p : Z ⟶ S) [IsFinite p] (s : S)
    (V : I → Scheme.{u}) (q : ∀ i, V i ⟶ Z) (Q : ∀ i, V i → Prop)
    [∀ i, Etale (q i)] [∀ i, IsSeparated (q i)]
    (hq : ∀ z : Z, p z = s →
      ∃ (i : I) (v : V i), q i v = z ∧ IsIso ((q i).residueFieldMap v) ∧ Q i v) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S), Etale g ∧
    ∃ u : U, g u = s ∧ IsIso (g.residueFieldMap u) ∧
    ∃ (n : ℕ) (F : Fin n → (pullback p g).Opens),
      (∀ j, IsClopen (F j : Set (pullback p g : Scheme)) ∧
        IsFinite ((F j).ι ≫ pullback.snd p g)) ∧
      Pairwise (fun i j ↦ Disjoint (F i) (F j)) ∧ (⨆ j, F j) = ⊤ ∧
    ∃ (label : Fin n → I) (b : ∀ j, (F j).toScheme ⟶ V (label j)),
      ∀ j, b j ≫ q (label j) = (F j).ι ≫ pullback.fst p g ∧
        ∃ v : V (label j), Q (label j) v ∧
          ∀ t : (F j).toScheme, ((F j).ι ≫ pullback.snd p g) t = u → b j t = v := by
  classical
  obtain ⟨U₀, g₀, hg₀, u₀, hu₀, hr₀, n, E, hEfin, hEdisj, hEtop, hEfib⟩ :=
    exists_nisnevich_finiteSplitting p s
  let pE (i : Fin n) : (E i).toScheme ⟶ U₀ := (E i).ι ≫ pullback.snd p g₀
  let aE (i : Fin n) : (E i).toScheme ⟶ Z := (E i).ι ≫ pullback.fst p g₀
  have hlocal (i : Fin n) :
      ∃ (U : Scheme.{u}) (g : U ⟶ U₀), Etale g ∧
      ∃ u : U, g u = u₀ ∧ IsIso (g.residueFieldMap u) ∧
      ∃ label : I, ∃ b : pullback (pE i) g ⟶ V label,
        b ≫ q label = pullback.fst (pE i) g ≫ aE i ∧
        ∃ v : V label, Q label v ∧
          ∀ t : (pullback (pE i) g : Scheme), pullback.snd (pE i) g t = u → b t = v := by
    obtain ⟨e, he, huniq⟩ := hEfib i
    have hp : p (aE i e) = s := by
      change p (pullback.fst p g₀ e.1) = s
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, he, hu₀]
    obtain ⟨label, v, hv, hr, hvQ⟩ := hq (aE i e) hp
    obtain ⟨t, ht₁, ht₂⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := q label) (g := aE i) v e hv
    have hrt := (q label).isIso_residueFieldMap_pullback_snd (aE i) v t ht₁
    have : IsFinite (pE i) := (hEfin i).2
    obtain ⟨U, g, hg, u, hu, hru, b, hb, hbval⟩ :=
      exists_nisnevich_lift_of_isFinite_singleton_with_point (pE i) u₀ e he huniq
        (pullback.snd (q label) (aE i)) t ht₂ hrt
    refine ⟨U, g, hg, u, hu, hru, label, b ≫ pullback.fst (q label) (aE i),
      ?_, v, hvQ, ?_⟩
    · rw [Category.assoc, pullback.condition, ← Category.assoc, hb]
    · intro t' ht'
      change pullback.fst (q label) (aE i) (b t') = v
      rw [hbval t' ht', ht₁]
  choose U g hg u hu hr label b hb v hvQ hbval using hlocal
  obtain ⟨W, h, hh, w, hw, hwr, τ, hτ, hτw⟩ :=
    exists_common_nisnevich_refinement u₀ n U g hg u hu hr
  let g' : W ⟶ S := h ≫ g₀
  let k : pullback p g' ⟶ pullback p g₀ :=
    pullback.map p g' p g₀ (𝟙 Z) h (𝟙 S) (by simp) (by simp [g'])
  have hk₁ : k ≫ pullback.fst p g₀ = pullback.fst p g' := by simp [k]
  have hk₂ : k ≫ pullback.snd p g₀ = pullback.snd p g' ≫ h := by simp [k]
  let F (i : Fin n) : (pullback p g').Opens := k ⁻¹ᵁ E i
  have hFclosed (i : Fin n) : IsClopen (F i : Set (pullback p g' : Scheme)) :=
    (hEfin i).1.preimage k.continuous
  have hFfinite (i : Fin n) : IsFinite ((F i).ι ≫ pullback.snd p g') := by
    have : IsClosedImmersion (F i).ι := .of_isPreimmersion _ (by
      simpa only [Scheme.Opens.range_ι] using (hFclosed i).1)
    infer_instance
  have hFdisj : Pairwise (fun i j ↦ Disjoint (F i) (F j)) := by
    intro i j hij
    change Disjoint (k ⁻¹ᵁ E i) (k ⁻¹ᵁ E j)
    rw [disjoint_iff, ← Scheme.Hom.preimage_inf, disjoint_iff.mp (hEdisj hij),
      Scheme.Hom.preimage_bot]
  have hFtop : (⨆ i, F i) = ⊤ := k.iSup_preimage_eq_top hEtop
  have hlift (i : Fin n) :
      ∃ c : (F i).toScheme ⟶ V (label i),
        c ≫ q (label i) = (F i).ι ≫ pullback.fst p g' ∧
        ∀ z : (F i).toScheme, ((F i).ι ≫ pullback.snd p g') z = w → c z = v i := by
    have hki : Set.range ((F i).ι ≫ k) ⊆ Set.range (E i).ι := by
      rintro x ⟨x', rfl⟩
      rw [Scheme.Opens.range_ι]
      exact x'.property
    let j : (F i).toScheme ⟶ (E i).toScheme :=
      IsOpenImmersion.lift (E i).ι ((F i).ι ≫ k) hki
    have hj : j ≫ (E i).ι = (F i).ι ≫ k :=
      IsOpenImmersion.lift_fac (E i).ι ((F i).ι ≫ k) hki
    have ht : j ≫ pE i = ((F i).ι ≫ pullback.snd p g' ≫ τ i) ≫ g i := by
      dsimp [pE]
      rw [← Category.assoc, hj]
      simp only [Category.assoc, hk₂, hτ]
    let t : (F i).toScheme ⟶ pullback (pE i) (g i) :=
      pullback.lift j ((F i).ι ≫ pullback.snd p g' ≫ τ i) ht
    refine ⟨t ≫ b i, ?_, ?_⟩
    · rw [Category.assoc, hb, ← Category.assoc, pullback.lift_fst]
      change j ≫ (E i).ι ≫ pullback.fst p g₀ = (F i).ι ≫ pullback.fst p g'
      rw [← Category.assoc, hj, Category.assoc, hk₁]
    · intro z hz
      apply hbval i (t z)
      have ht₂ : t ≫ pullback.snd (pE i) (g i) =
          (F i).ι ≫ pullback.snd p g' ≫ τ i := pullback.lift_snd _ _ _
      have h := congrArg (fun f : (F i).toScheme ⟶ U i ↦ f z) ht₂
      change pullback.snd (pE i) (g i) (t z) =
        τ i (((F i).ι ≫ pullback.snd p g') z) at h
      simpa only [hz, hτw] using h
  choose c hc hcv using hlift
  refine ⟨W, g', inferInstance, w, ?_, ?_, n, F,
    fun i ↦ ⟨hFclosed i, hFfinite i⟩, hFdisj, hFtop, label, c,
    fun i ↦ ⟨hc i, v i, hvQ i, hcv i⟩⟩
  · change g₀ (h w) = s
    rwa [hw]
  · rw [Scheme.residueFieldMap_comp]
    have : IsIso (g₀.residueFieldMap (h w)) := by rw [hw]; exact hr₀
    infer_instance

/-- The original whole-support finite-family endpoint is the same construction
with the unrestricted condition on its chosen residue-lift points. -/
theorem exists_nisnevich_family_lift_of_isFinite
    {I : Type v} {Z S : Scheme.{u}} (p : Z ⟶ S) [IsFinite p] (s : S)
    (V : I → Scheme.{u}) (q : ∀ i, V i ⟶ Z)
    [∀ i, Etale (q i)] [∀ i, IsSeparated (q i)]
    (hq : ∀ z : Z, p z = s →
      ∃ (i : I) (v : V i), q i v = z ∧ IsIso ((q i).residueFieldMap v)) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S), Etale g ∧
    ∃ u : U, g u = s ∧ IsIso (g.residueFieldMap u) ∧
    ∃ (n : ℕ) (F : Fin n → (pullback p g).Opens),
      (∀ j, IsClopen (F j : Set (pullback p g : Scheme)) ∧
        IsFinite ((F j).ι ≫ pullback.snd p g)) ∧
      Pairwise (fun i j ↦ Disjoint (F i) (F j)) ∧ (⨆ j, F j) = ⊤ ∧
    ∃ (label : Fin n → I) (b : ∀ j, (F j).toScheme ⟶ V (label j)),
      ∀ j, b j ≫ q (label j) = (F j).ι ≫ pullback.fst p g := by
  have hq' : ∀ z : Z, p z = s → ∃ (i : I) (v : V i),
      q i v = z ∧ IsIso ((q i).residueFieldMap v) ∧ True := by
    intro z hz
    obtain ⟨i, v, hv, hr⟩ := hq z hz
    exact ⟨i, v, hv, hr, trivial⟩
  obtain ⟨U, g, hg, u, hu, hr, n, F, hF, hd, ht, label, b, hb⟩ :=
    exists_nisnevich_family_lift_of_isFinite_with_point_property p s V q (fun _ _ ↦ True) hq'
  exact ⟨U, g, hg, u, hu, hr, n, F, hF, hd, ht, label, b, fun j ↦ (hb j).1⟩

end AlgebraicGeometry
