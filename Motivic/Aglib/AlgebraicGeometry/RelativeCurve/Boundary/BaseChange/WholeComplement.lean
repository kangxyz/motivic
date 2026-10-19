/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.Cover
/-! # The full Nisnevich complement after restriction only of the base -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Hom
variable {S X Y A Z : Scheme.{u}} (q : X ⟶ S) (p : Y ⟶ X) (a : A ⟶ X)
  (z : Z ⟶ X) [IsClosedImmersion z] (V : S.Opens)

abbrev boundaryBaseWholeLift := boundaryBaseLift q z ⊤ V (fun _ _ => trivial)

instance boundaryBaseWholeLift_closed : IsClosedImmersion (boundaryBaseWholeLift q z V) :=
  MorphismProperty.of_isPullback
    (boundaryBaseLift_isPullback q z ⊤ V (fun _ _ => trivial)).flip inferInstance

omit [IsClosedImmersion z] in
lemma mem_range_boundaryBaseWholeLift (x : (boundaryBaseSourceOpen q ⊤ V).toScheme) :
    x ∈ Set.range (boundaryBaseWholeLift q z V) ↔
      (boundaryBaseSourceOpen q ⊤ V).ι x ∈ Set.range z := by
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b.val, (congrArg (fun f => f b)
      (boundaryBaseLift_ι q z ⊤ V (fun _ _ => trivial))).symm⟩
  · rintro ⟨b, hb⟩
    have hbV : (z ≫ q) b ∈ V := by
      change q (z b) ∈ V
      rw [hb]
      exact x.property.2
    refine ⟨⟨b, hbV⟩, ?_⟩
    apply (boundaryBaseSourceOpen q ⊤ V).ι.isOpenEmbedding.injective
    change ((boundaryBaseWholeLift q z V ≫ (boundaryBaseSourceOpen q ⊤ V).ι) ⟨b, hbV⟩) = _
    rw [boundaryBaseLift_ι]
    exact hb

lemma mem_range_boundaryBaseCoverMap (x : (boundaryBaseSourceOpen q ⊤ V).toScheme) :
    x ∈ Set.range (boundaryBaseCoverMap q a ⊤ V) ↔
      (boundaryBaseSourceOpen q ⊤ V).ι x ∈ Set.range a := by
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b.val, (congrArg (fun f => f b)
      (morphismRestrict_ι a (boundaryBaseSourceOpen q ⊤ V))).symm⟩
  · rintro ⟨b, hb⟩
    have hbW : a b ∈ boundaryBaseSourceOpen q ⊤ V := by rw [hb]; exact x.property
    refine ⟨⟨b, hbW⟩, ?_⟩
    apply (boundaryBaseSourceOpen q ⊤ V).ι.isOpenEmbedding.injective
    change ((boundaryBaseCoverMap q a ⊤ V ≫ (boundaryBaseSourceOpen q ⊤ V).ι) ⟨b, hbW⟩) = _
    rw [morphismRestrict_ι]
    exact hb

omit [IsClosedImmersion z] in
lemma boundaryBaseWholeLift_range
    (hcomp : Set.range z = (Set.range a)ᶜ) :
    Set.range (boundaryBaseWholeLift q z V) = (Set.range (boundaryBaseCoverMap q a ⊤ V))ᶜ := by
  ext x
  rw [Set.mem_compl_iff, mem_range_boundaryBaseWholeLift, mem_range_boundaryBaseCoverMap, hcomp]
  rfl

omit [IsClosedImmersion z] in
lemma boundaryBaseWholeLift_iso (s : Z ⟶ Y) (hs : s ≫ p = z)
    (H : IsPullback s (𝟙 Z) p z) :
    IsIso (pullback.snd (boundaryBaseCoverMap q p ⊤ V) (boundaryBaseWholeLift q z V)) := by
  let H' := boundaryBaseCoverLift_isPullback q p z s hs ⊤ V (fun _ _ => trivial) H
  have he := H'.isoPullback_hom_snd
  have : IsIso (H'.isoPullback.hom ≫
      pullback.snd (boundaryBaseCoverMap q p ⊤ V) (boundaryBaseWholeLift q z V)) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_left H'.isoPullback.hom _

end AlgebraicGeometry.Scheme.Hom
