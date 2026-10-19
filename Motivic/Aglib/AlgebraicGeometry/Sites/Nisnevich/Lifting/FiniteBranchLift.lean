/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Nisnevich.Lifting.FiniteSplitting
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.FiniteEtaleNeighborhoodIso
public import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Lifting a finite support with one distinguished branch

The support may have nilpotents and arbitrary residue-field extensions over
the base. The isomorphism-neighborhood argument is applied over the support,
and finite closed-image removal then shrinks the original base.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Étale morphisms are locally quasi-finite. -/
lemma Scheme.Hom.locallyQuasiFinite_of_etale
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] : LocallyQuasiFinite f := by
  constructor
  intro U hU V hV e
  have h := f.etale_appLE hU hV e
  algebraize [(f.appLE U V e).hom]
  exact RingHom.quasiFinite_algebraMap.mpr inferInstance

/-- Surjectivity on stalks identifies the actual residue fields. -/
lemma Scheme.Hom.isIso_residueFieldMap_of_surjectiveOnStalks
    {X Y : Scheme.{u}} (f : X ⟶ Y) [SurjectiveOnStalks f] (x : X) :
    IsIso (f.residueFieldMap x) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine ⟨(f.residueFieldMap x).hom.injective, ?_⟩
  have h := (X.residue_surjective x).comp (f.stalkMap_surjective x)
  change Function.Surjective (f.stalkMap x ≫ X.residue x) at h
  rw [← Scheme.residue_residueFieldMap] at h
  change Function.Surjective ((f.residueFieldMap x) ∘ (Y.residue (f x))) at h
  exact h.of_comp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The fiber of a pointed residue-field-isomorphism base change still embeds
in the original source, with its full scheme structure. -/
lemma Scheme.Hom.isPreimmersion_fiberι_comp_pullback_fst
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (y : Y)
    [IsIso (g.residueFieldMap y)] :
    IsPreimmersion ((pullback.snd f g).fiberι y ≫ pullback.fst f g) := by
  let a : (pullback.snd f g).fiber y ⟶ f.fiber (g y) :=
    pullback.map (pullback.snd f g) (Y.fromSpecResidueField y)
    f (S.fromSpecResidueField (g y)) (pullback.fst f g)
    (Spec.map (g.residueFieldMap y)) g pullback.condition.symm (by simp)
  have ha := isPullback_fiberToSpecResidueField_of_isPullback
    (IsPullback.of_hasPullback f g) y
  have : IsIso a := ha.isIso_fst_of_isIso
  have he : (pullback.snd f g).fiberι y ≫ pullback.fst f g =
      a ≫ f.fiberι (g y) := by simp [a, Scheme.Hom.fiberι]
  rw [he]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Pulling back along a morphism with an isomorphic actual residue-field map
preserves the actual residue field at every point over the chosen point. -/
lemma Scheme.Hom.isIso_residueFieldMap_pullback_fst
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (y : Y)
    [IsIso (g.residueFieldMap y)] (t : (pullback f g : Scheme))
    (ht : pullback.snd f g t = y) :
    IsIso ((pullback.fst f g).residueFieldMap t) := by
  let z := ((pullback.snd f g).fiberHomeo y).symm ⟨t, ht⟩
  have hz : (pullback.snd f g).fiberι y z = t :=
    (pullback.snd f g).fiberι_fiberHomeo_symm y ⟨t, ht⟩
  have := f.isPreimmersion_fiberι_comp_pullback_fst g y
  have hcomp := Scheme.Hom.isIso_residueFieldMap_of_surjectiveOnStalks
    ((pullback.snd f g).fiberι y ≫ pullback.fst f g) z
  have := Scheme.Hom.isIso_residueFieldMap_of_surjectiveOnStalks
    ((pullback.snd f g).fiberι y) z
  rw [Scheme.residueFieldMap_comp] at hcomp
  rw [← hz]
  exact IsIso.of_isIso_comp_right _ (((pullback.snd f g).fiberι y).residueFieldMap z)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Over a point where the actual base-change residue map is an isomorphism,
the two projections uniquely determine a pullback point. -/
lemma Scheme.Hom.pullback_point_ext_of_residueFieldIso
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (y : Y)
    [IsIso (g.residueFieldMap y)] (t t' : (pullback f g : Scheme))
    (ht : pullback.snd f g t = y) (ht' : pullback.snd f g t' = y)
    (he : pullback.fst f g t = pullback.fst f g t') : t = t' := by
  let z := ((pullback.snd f g).fiberHomeo y).symm ⟨t, ht⟩
  let z' := ((pullback.snd f g).fiberHomeo y).symm ⟨t', ht'⟩
  have hz : (pullback.snd f g).fiberι y z = t :=
    (pullback.snd f g).fiberι_fiberHomeo_symm y ⟨t, ht⟩
  have hz' : (pullback.snd f g).fiberι y z' = t' :=
    (pullback.snd f g).fiberι_fiberHomeo_symm y ⟨t', ht'⟩
  have := f.isPreimmersion_fiberι_comp_pullback_fst g y
  have hzz' : z = z' :=
    ((pullback.snd f g).fiberι y ≫ pullback.fst f g).isEmbedding.injective (by
      simpa only [Scheme.Hom.comp_apply, hz, hz'] using he)
  exact hz.symm.trans ((congrArg ((pullback.snd f g).fiberι y) hzz').trans hz')

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A separated étale lift of the unique point of a finite fiber extends to
the entire pulled-back finite support over a genuine pointed Nisnevich
neighborhood. No flatness or reducedness of the finite support is required. -/
theorem exists_nisnevich_lift_of_isFinite_singleton_with_point
    {Z V S : Scheme.{u}} (p : Z ⟶ S) [IsFinite p]
    (s : S) (z : Z) (hz : p z = s)
    (huniq : ∀ z' : Z, p z' = s → z' = z)
    (q : V ⟶ Z) [Etale q] [IsSeparated q]
    (v : V) (hv : q v = z) (hres : IsIso (q.residueFieldMap v)) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S), Etale g ∧
    ∃ u : U, g u = s ∧ IsIso (g.residueFieldMap u) ∧
    ∃ b : pullback p g ⟶ V, b ≫ q = pullback.fst p g ∧
      ∀ t : (pullback p g : Scheme), pullback.snd p g t = u → b t = v := by
  have := q.locallyQuasiFinite_of_etale
  obtain ⟨U, g, hg, u, hu, hgu, E, _, e, _, hE, hev, heu, hEuniq⟩ :=
    exists_nisnevich_isCompl_of_quasiFiniteAt (q ≫ p)
      (by simpa only [Scheme.Hom.comp_apply, hv] using hz)
      ((q ≫ p).quasiFiniteAt v)
  let r : pullback (q ≫ p) g ⟶ pullback p g :=
    (pullbackRightPullbackFstIso p g q).inv ≫ pullback.snd q (pullback.fst p g)
  have hr₁ : r ≫ pullback.fst p g = pullback.fst (q ≫ p) g ≫ q := by simp [r]
  have hr₂ : r ≫ pullback.snd p g = pullback.snd (q ≫ p) g := by simp [r]
  have : Etale r := by dsimp [r]; infer_instance
  let a : E.toScheme ⟶ pullback p g := E.ι ≫ r
  have ha₂ : a ≫ pullback.snd p g = E.ι ≫ pullback.snd (q ≫ p) g := by
    simp [a, hr₂]
  have ha₁ : a ≫ pullback.fst p g = E.ι ≫ pullback.fst (q ≫ p) g ≫ q := by
    simp [a, hr₁]
  have : IsFinite (a ≫ pullback.snd p g) := by rw [ha₂]; exact hE
  have : IsFinite a := .of_comp a (pullback.snd p g)
  have hae : pullback.snd p g (a e) = u := by
    rw [← Scheme.Hom.comp_apply, ha₂]
    exact heu
  have hpa : pullback.fst p g (a e) = z := by
    rw [← Scheme.Hom.comp_apply, ha₁]
    change q (pullback.fst (q ≫ p) g e.1) = z
    rwa [hev]
  have htuniq : ∀ t : (pullback p g : Scheme), pullback.snd p g t = u → t = a e := by
    intro t ht
    apply p.pullback_point_ext_of_residueFieldIso g u t (a e) ht hae
    rw [hpa]
    apply huniq
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, ht, hu]
  have haeuniq : ∀ e' : E, a e' = a e → e' = e := by
    intro e' he'
    apply hEuniq
    have he'' := congrArg (pullback.snd p g) he'
    change (a ≫ pullback.snd p g) e' = (a ≫ pullback.snd p g) e at he''
    rw [ha₂] at he''
    exact he''.trans heu
  have hleft := (q ≫ p).isIso_residueFieldMap_pullback_fst g u e.1 heu
  have hfirst := p.isIso_residueFieldMap_pullback_fst g u (a e) hae
  have hq : IsIso (q.residueFieldMap (pullback.fst (q ≫ p) g e.1)) := by
    rw [hev]
    exact hres
  have hcomp : IsIso ((a ≫ pullback.fst p g).residueFieldMap e) := by
    rw [ha₁, Scheme.residueFieldMap_comp, Scheme.residueFieldMap_comp]
    change IsIso (q.residueFieldMap (pullback.fst (q ≫ p) g e.1) ≫
      (pullback.fst (q ≫ p) g).residueFieldMap e.1 ≫ E.ι.residueFieldMap e)
    infer_instance
  rw [Scheme.residueFieldMap_comp] at hcomp
  have hares : IsIso (a.residueFieldMap e) :=
    IsIso.of_isIso_comp_left ((pullback.fst p g).residueFieldMap (a e)) _
  obtain ⟨O, heO, hO⟩ := a.exists_isIso_morphismRestrict_of_singleton
    (a e) e rfl haeuniq hares
  obtain ⟨W, huW, hW⟩ := exists_open_preimage_disjoint_of_isFinite (pullback.snd p g)
    (O : Set (pullback p g : Scheme))ᶜ O.isOpen.isClosed_compl u (by
      intro t ht htu
      exact ht ((htuniq t htu) ▸ heO))
  let g' : W.toScheme ⟶ S := W.ι ≫ g
  let k : pullback p g' ⟶ pullback p g :=
    pullback.map p g' p g (𝟙 Z) W.ι (𝟙 S) (by simp) (by simp [g'])
  have hk : Set.range k ⊆ Set.range O.ι := by
    rintro t ⟨t', rfl⟩
    rw [Scheme.Opens.range_ι]
    by_contra hn
    apply Set.disjoint_left.mp hW ?_ hn
    change pullback.snd p g (k t') ∈ W
    rw [← Scheme.Hom.comp_apply]
    simp [k]
  let l : pullback p g' ⟶ O.toScheme := IsOpenImmersion.lift O.ι k hk
  have hl : l ≫ O.ι = k := IsOpenImmersion.lift_fac O.ι k hk
  let b : pullback p g' ⟶ V :=
    l ≫ inv (a ∣_ O) ≫ (a ⁻¹ᵁ O).ι ≫ E.ι ≫ pullback.fst (q ≫ p) g
  let bE : pullback p g' ⟶ E.toScheme := l ≫ inv (a ∣_ O) ≫ (a ⁻¹ᵁ O).ι
  have hbE : bE ≫ a = k := by
    change l ≫ inv (a ∣_ O) ≫ (a ⁻¹ᵁ O).ι ≫ a = k
    rw [← morphismRestrict_ι]
    simp only [IsIso.inv_hom_id_assoc]
    exact hl
  refine ⟨W, g', inferInstance, ⟨u, huW⟩, hu, ?_, b, ?_, ?_⟩
  · rw [Scheme.residueFieldMap_comp]
    change IsIso (g.residueFieldMap u ≫ W.ι.residueFieldMap ⟨u, huW⟩)
    infer_instance
  · change l ≫ inv (a ∣_ O) ≫ (a ⁻¹ᵁ O).ι ≫ E.ι ≫
      pullback.fst (q ≫ p) g ≫ q = pullback.fst p g'
    rw [← ha₁, ← Category.assoc (a ⁻¹ᵁ O).ι a,
      ← morphismRestrict_ι]
    simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    rw [← Category.assoc, hl]
    simp [k]
  · intro t ht
    have hk₂ : k ≫ pullback.snd p g = pullback.snd p g' ≫ W.ι := by simp [k]
    have hkt : pullback.snd p g (k t) = u := by
      have h := congrArg (fun f : pullback p g' ⟶ U ↦ f t) hk₂
      change pullback.snd p g (k t) = W.ι (pullback.snd p g' t) at h
      rw [ht] at h
      exact h
    have hbEt : bE t = e := by
      apply haeuniq
      exact (congrArg (fun f : pullback p g' ⟶ pullback p g ↦ f t) hbE).trans
        (htuniq (k t) hkt)
    change pullback.fst (q ≫ p) g (E.ι (bE t)) = v
    rw [hbEt]
    exact hev

/-- The original whole-support lifting endpoint, projected from the same
construction that also preserves the exact input residue-field lift. -/
theorem exists_nisnevich_lift_of_isFinite_singleton
    {Z V S : Scheme.{u}} (p : Z ⟶ S) [IsFinite p]
    (s : S) (z : Z) (hz : p z = s)
    (huniq : ∀ z' : Z, p z' = s → z' = z)
    (q : V ⟶ Z) [Etale q] [IsSeparated q]
    (v : V) (hv : q v = z) (hres : IsIso (q.residueFieldMap v)) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S), Etale g ∧
    ∃ u : U, g u = s ∧ IsIso (g.residueFieldMap u) ∧
    ∃ b : pullback p g ⟶ V, b ≫ q = pullback.fst p g := by
  obtain ⟨U, g, hg, u, hu, hr, b, hb, _⟩ :=
    exists_nisnevich_lift_of_isFinite_singleton_with_point p s z hz huniq q v hv hres
  exact ⟨U, g, hg, u, hu, hr, b, hb⟩

end AlgebraicGeometry
