/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Nisnevich.Lifting.FiniteBranchLift
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Nisnevich lifting on an entire finite support

A finite support is first partitioned into finitely many clopen pieces near
the chosen base point. Their actual étale lifts are put over a common pointed
Nisnevich neighborhood and glued on the whole pulled-back support.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The symmetric form of actual residue-field preservation under pointed
base change. -/
lemma Scheme.Hom.isIso_residueFieldMap_pullback_snd
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (x : X)
    [IsIso (f.residueFieldMap x)] (t : (pullback f g : Scheme))
    (ht : pullback.fst f g t = x) :
    IsIso ((pullback.snd f g).residueFieldMap t) := by
  let e := pullbackSymmetry f g
  have he : pullback.snd g f (e.hom t) = x := by
    rw [← Scheme.Hom.comp_apply]
    simpa [e] using ht
  have := g.isIso_residueFieldMap_pullback_fst f x (e.hom t) he
  have h : IsIso ((e.hom ≫ pullback.fst g f).residueFieldMap t) := by
    rw [Scheme.residueFieldMap_comp]
    infer_instance
  change IsIso (((pullbackSymmetry f g).hom ≫ pullback.fst g f).residueFieldMap t) at h
  rwa [pullbackSymmetry_hom_comp_fst] at h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A finite family of pointed Nisnevich neighborhoods admits a common
pointed Nisnevich refinement, with actual maps to every member. -/
theorem exists_common_nisnevich_refinement
    {S : Scheme.{u}} (s : S) (n : ℕ)
    (U : Fin n → Scheme.{u}) (g : ∀ i, U i ⟶ S)
    (hg : ∀ i, Etale (g i)) (u : ∀ i, U i)
    (hu : ∀ i, g i (u i) = s)
    (hres : ∀ i, IsIso ((g i).residueFieldMap (u i))) :
    ∃ (W : Scheme.{u}) (h : W ⟶ S), Etale h ∧
    ∃ w : W, h w = s ∧ IsIso (h.residueFieldMap w) ∧
    ∃ a : ∀ i, W ⟶ U i, (∀ i, a i ≫ g i = h) ∧ (∀ i, a i w = u i) := by
  induction n with
  | zero =>
    exact ⟨S, 𝟙 S, inferInstance, s, rfl, inferInstance,
      (fun i ↦ Fin.elim0 i), (fun i ↦ Fin.elim0 i), (fun i ↦ Fin.elim0 i)⟩
  | succ n ih =>
    obtain ⟨W, h, hh, w, hw, hwr, a, ha, haw⟩ :=
      ih (fun i ↦ U i.succ) (fun i ↦ g i.succ) (fun i ↦ hg i.succ)
        (fun i ↦ u i.succ) (fun i ↦ hu i.succ) (fun i ↦ hres i.succ)
    have := hg 0
    have := hres 0
    obtain ⟨w', hw'₁, hw'₂⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := h) (g := g 0) w (u 0) (hw.trans (hu 0).symm)
    have := h.isIso_residueFieldMap_pullback_fst (g 0) (u 0) w' hw'₂
    let h' := pullback.fst h (g 0) ≫ h
    have hh'w : h' w' = s := by
      change h (pullback.fst h (g 0) w') = s
      rwa [hw'₁]
    have hh'res : IsIso (h'.residueFieldMap w') := by
      rw [Scheme.residueFieldMap_comp]
      have : IsIso (h.residueFieldMap (pullback.fst h (g 0) w')) := by
        rw [hw'₁]
        exact hwr
      infer_instance
    refine ⟨pullback h (g 0), h', inferInstance, w', hh'w, hh'res,
      Fin.cases (pullback.snd h (g 0)) (fun i ↦ pullback.fst h (g 0) ≫ a i),
      ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · exact pullback.condition.symm
      · change (pullback.fst h (g 0) ≫ a j) ≫ g j.succ = h'
        dsimp [h']
        rw [Category.assoc, ha]
    · intro i
      refine Fin.cases hw'₂ (fun j ↦ ?_) i
      change a j (pullback.fst h (g 0) w') = u j.succ
      rw [hw'₁]
      exact haw j

/-- Actual lifts on a pairwise disjoint open cover glue to a global lift, with the
prescribed restriction on every member of the cover. -/
lemma Scheme.exists_lift_of_disjoint_openCover
    {X V Z : Scheme.{u}} (a : X ⟶ Z) (q : V ⟶ Z)
    {I : Type v} (E : I → X.Opens)
    (hdisj : Pairwise fun i j ↦ Disjoint (E i) (E j))
    (hcover : iSup E = ⊤) (b : ∀ i, (E i).toScheme ⟶ V)
    (hb : ∀ i, b i ≫ q = (E i).ι ≫ a) :
    ∃ f : X ⟶ V, f ≫ q = a ∧ ∀ i, (E i).ι ≫ f = b i := by
  let 𝒰 := X.openCoverOfIsOpenCover E hcover
  have hcompat : ∀ i j,
      pullback.fst (𝒰.f i) (𝒰.f j) ≫ b i = pullback.snd _ _ ≫ b j := by
    intro i j
    change pullback.fst (E i).ι (E j).ι ≫ b i = pullback.snd _ _ ≫ b j
    by_cases hij : i = j
    · subst j
      have he : pullback.fst (E i).ι (E i).ι = pullback.snd (E i).ι (E i).ι :=
        (cancel_mono (E i).ι).mp pullback.condition
      rw [he]
    · have : IsEmpty (pullback (E i).ι (E j).ι : Scheme) :=
        Scheme.isEmpty_pullback_iff.mpr (by
          simpa only [Scheme.Opens.range_ι] using
            (TopologicalSpace.Opens.coe_disjoint.mpr (hdisj hij)))
      exact isInitialOfIsEmpty.hom_ext _ _
  refine ⟨𝒰.glueMorphisms b hcompat, ?_, ?_⟩
  · apply 𝒰.hom_ext
    intro i
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f : (E i).toScheme ⟶ V ↦ f ≫ q)
        (𝒰.ι_glueMorphisms b hcompat i)).trans (hb i))
  · intro i
    exact 𝒰.ι_glueMorphisms b hcompat i


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A separated étale morphism that has an actual residue-field-isomorphism
lift at every point of one finite fiber lifts the entire finite support after
a pointed Nisnevich base change. Empty fibers and nonreduced supports are
included, and no separability or flatness of the finite morphism is assumed. -/
theorem exists_nisnevich_lift_of_isFinite
    {Z V S : Scheme.{u}} (p : Z ⟶ S) [IsFinite p] (s : S)
    (q : V ⟶ Z) [Etale q] [IsSeparated q]
    (hq : ∀ z : Z, p z = s → ∃ v : V, q v = z ∧ IsIso (q.residueFieldMap v)) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S), Etale g ∧
    ∃ u : U, g u = s ∧ IsIso (g.residueFieldMap u) ∧
    ∃ b : pullback p g ⟶ V, b ≫ q = pullback.fst p g := by
  classical
  obtain ⟨U₀, g₀, hg₀, u₀, hu₀, hr₀, n, E, hEfin, hEdisj, hEtop, hEfib⟩ :=
    exists_nisnevich_finiteSplitting p s
  let pE (i : Fin n) : (E i).toScheme ⟶ U₀ := (E i).ι ≫ pullback.snd p g₀
  let aE (i : Fin n) : (E i).toScheme ⟶ Z := (E i).ι ≫ pullback.fst p g₀
  have hlocal (i : Fin n) :
      ∃ (U : Scheme.{u}) (g : U ⟶ U₀), Etale g ∧
      ∃ u : U, g u = u₀ ∧ IsIso (g.residueFieldMap u) ∧
      ∃ b : pullback (pE i) g ⟶ V, b ≫ q = pullback.fst (pE i) g ≫ aE i := by
    obtain ⟨e, he, huniq⟩ := hEfib i
    have hp : p (aE i e) = s := by
      change p (pullback.fst p g₀ e.1) = s
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, he, hu₀]
    obtain ⟨v, hv, hr⟩ := hq (aE i e) hp
    obtain ⟨t, ht₁, ht₂⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := q) (g := aE i) v e hv
    have hrt := q.isIso_residueFieldMap_pullback_snd (aE i) v t ht₁
    have : IsFinite (pE i) := (hEfin i).2
    obtain ⟨U, g, hg, u, hu, hru, b, hb⟩ :=
      exists_nisnevich_lift_of_isFinite_singleton (pE i) u₀ e he huniq
        (pullback.snd q (aE i)) t ht₂ hrt
    refine ⟨U, g, hg, u, hu, hru, b ≫ pullback.fst q (aE i), ?_⟩
    rw [Category.assoc, pullback.condition, ← Category.assoc, hb]
  choose U g hg u hu hr b hb using hlocal
  obtain ⟨W, h, hh, w, hw, hwr, τ, hτ, hτw⟩ :=
    exists_common_nisnevich_refinement u₀ n U g hg u hu hr
  let g' : W ⟶ S := h ≫ g₀
  let k : pullback p g' ⟶ pullback p g₀ :=
    pullback.map p g' p g₀ (𝟙 Z) h (𝟙 S) (by simp) (by simp [g'])
  have hk₁ : k ≫ pullback.fst p g₀ = pullback.fst p g' := by simp [k]
  have hk₂ : k ≫ pullback.snd p g₀ = pullback.snd p g' ≫ h := by simp [k]
  let F (i : Fin n) : (pullback p g').Opens := k ⁻¹ᵁ E i
  have hFdisj : Pairwise (fun i j ↦ Disjoint (F i) (F j)) := by
    intro i j hij
    change Disjoint (k ⁻¹ᵁ E i) (k ⁻¹ᵁ E j)
    rw [disjoint_iff, ← Scheme.Hom.preimage_inf, disjoint_iff.mp (hEdisj hij),
      Scheme.Hom.preimage_bot]
  have hFtop : (⨆ i, F i) = ⊤ := k.iSup_preimage_eq_top hEtop
  have hlift (i : Fin n) :
      ∃ c : (F i).toScheme ⟶ V, c ≫ q = (F i).ι ≫ pullback.fst p g' := by
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
    refine ⟨t ≫ b i, ?_⟩
    rw [Category.assoc, hb, ← Category.assoc, pullback.lift_fst]
    change j ≫ (E i).ι ≫ pullback.fst p g₀ = (F i).ι ≫ pullback.fst p g'
    rw [← Category.assoc, hj, Category.assoc, hk₁]
  choose c hc using hlift
  obtain ⟨b', hb', _⟩ := Scheme.exists_lift_of_disjoint_openCover
    (pullback.fst p g') q F hFdisj hFtop c hc
  refine ⟨W, g', inferInstance, w, ?_, ?_, b', hb'⟩
  · change g₀ (h w) = s
    rwa [hw]
  · rw [Scheme.residueFieldMap_comp]
    have : IsIso (g₀.residueFieldMap (h w)) := by rw [hw]; exact hr₀
    infer_instance

end AlgebraicGeometry
