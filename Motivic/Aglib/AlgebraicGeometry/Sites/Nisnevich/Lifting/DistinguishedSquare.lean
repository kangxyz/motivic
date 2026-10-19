/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Nisnevich.Lifting.FiniteBranchLift
public import Motivic.Aglib.CategoryTheory.Sites.DistinguishedSquare
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Field-valued descent for Nisnevich distinguished squares

An open immersion and an étale morphism which is an isomorphism over the closed
complement jointly lift field-valued points. Their right self-overlap is covered
by the diagonal and the double overlap over the open. The closed complement may
be given its reduced scheme structure; the proofs work for any closed immersion
with the stated support and base-change isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- A field-valued point whose image lies in a morphism surjective on stalks
factors through that morphism, with the same field of definition. -/
theorem exists_field_lift_of_mem_range {U X : Scheme.{u}} (f : U ⟶ X)
    [SurjectiveOnStalks f] {K : Type u} [Field K] (x : Spec (.of K) ⟶ X)
    (hx : x (IsLocalRing.closedPoint K) ∈ Set.range f) :
    ∃ y : Spec (.of K) ⟶ U, y ≫ f = x := by
  obtain ⟨y, hy⟩ := hx
  have := f.isIso_residueFieldMap_of_surjectiveOnStalks y
  let a : Spec (X.residueField (f y)) ⟶ U :=
    Spec.map (inv (f.residueFieldMap y)) ≫ U.fromSpecResidueField y
  have ha : a ≫ f = X.fromSpecResidueField (f y) := by
    dsimp [a]
    rw [Category.assoc, ← f.SpecMap_residueFieldMap_fromSpecResidueField,
      ← Category.assoc, ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id, Category.id_comp]
  have hlift : ∃ b : Spec (X.residueField (x (IsLocalRing.closedPoint K))) ⟶ U,
      b ≫ f = X.fromSpecResidueField (x (IsLocalRing.closedPoint K)) := by
    rw [← hy]
    exact ⟨a, ha⟩
  obtain ⟨b, hb⟩ := hlift
  refine ⟨Spec.map (X.descResidueField (stalkClosedPointTo x)) ≫ b, ?_⟩
  rw [Category.assoc, hb]
  exact X.descResidueField_stalkClosedPointTo_fromSpecResidueField K x

/-- Every field-valued point factors through an open immersion or its closed
complement. This assertion includes residue-field preservation. -/
theorem exists_field_lift_open_or_closed {A X Z : Scheme.{u}}
    (i : A ⟶ X) [IsOpenImmersion i] (z : Z ⟶ X) [IsClosedImmersion z]
    (hcomp : Set.range z = (Set.range i)ᶜ)
    {K : Type u} [Field K] (x : Spec (.of K) ⟶ X) :
    (∃ a : Spec (.of K) ⟶ A, a ≫ i = x) ∨
      (∃ c : Spec (.of K) ⟶ Z, c ≫ z = x) := by
  by_cases h : x (IsLocalRing.closedPoint K) ∈ Set.range i
  · exact Or.inl (exists_field_lift_of_mem_range i x h)
  · exact Or.inr (exists_field_lift_of_mem_range z x (hcomp ▸ h))

/-- An isomorphism over the closed complement makes the open and étale arrows
jointly lift every field-valued point. -/
theorem exists_field_lift_open_or_etale {A X Y Z : Scheme.{u}}
    (i : A ⟶ X) [IsOpenImmersion i] (p : Y ⟶ X)
    (z : Z ⟶ X) [IsClosedImmersion z]
    (hcomp : Set.range z = (Set.range i)ᶜ) [IsIso (pullback.snd p z)]
    {K : Type u} [Field K] (x : Spec (.of K) ⟶ X) :
    (∃ a : Spec (.of K) ⟶ A, a ≫ i = x) ∨
      (∃ y : Spec (.of K) ⟶ Y, y ≫ p = x) := by
  obtain h | ⟨c, hc⟩ := exists_field_lift_open_or_closed i z hcomp x
  · exact Or.inl h
  · right
    refine ⟨c ≫ inv (pullback.snd p z) ≫ pullback.fst p z, ?_⟩
    simp only [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc, hc]

/-- Two lifts of the same map through an étale neighborhood agree whenever that
map factors through a closed subscheme over which the neighborhood is an isomorphism. -/
theorem eq_of_comp_eq_over_iso_complement {T Y X Z : Scheme.{u}}
    (p : Y ⟶ X) (z : Z ⟶ X) [IsIso (pullback.snd p z)]
    (a b : T ⟶ Y) (c : T ⟶ Z)
    (ha : a ≫ p = c ≫ z) (hb : b ≫ p = c ≫ z) : a = b := by
  have h : pullback.lift a c ha = pullback.lift b c hb := by
    apply (cancel_mono (pullback.snd p z)).mp
    rw [pullback.lift_snd, pullback.lift_snd]
  have := h =≫ pullback.fst p z
  simpa only [pullback.lift_fst] using this

/-- The right self-overlap of a distinguished square is jointly covered by its
actual diagonal and the double overlap over the open. Arbitrary limiting cones
are allowed so that this theorem applies after forgetting a geometric site. -/
theorem exists_field_lift_diagonal_or_overlap
    (sq : Square Scheme.{u}) (hpb : sq.IsPullback)
    [IsOpenImmersion sq.f₂₄] {Z : Scheme.{u}} (z : Z ⟶ sq.X₄)
    [IsClosedImmersion z] (hcomp : Set.range z = (Set.range sq.f₂₄)ᶜ)
    [IsIso (pullback.snd sq.f₃₄ z)]
    {D E : Scheme.{u}} (d₁ d₂ : D ⟶ sq.X₃)
    (hD : IsPullback d₁ d₂ sq.f₃₄ sq.f₃₄)
    (e₁ e₂ : E ⟶ sq.X₁) (hE : IsPullback e₁ e₂ sq.f₁₂ sq.f₁₂)
    (d : sq.X₃ ⟶ D) (hd₁ : d ≫ d₁ = 𝟙 _) (hd₂ : d ≫ d₂ = 𝟙 _)
    (e : E ⟶ D) (he₁ : e ≫ d₁ = e₁ ≫ sq.f₁₃)
    (he₂ : e ≫ d₂ = e₂ ≫ sq.f₁₃)
    {K : Type u} [Field K] (t : Spec (.of K) ⟶ D) :
    (∃ y : Spec (.of K) ⟶ sq.X₃, y ≫ d = t) ∨
      (∃ b : Spec (.of K) ⟶ E, b ≫ e = t) := by
  obtain ⟨a, ha⟩ | ⟨c, hc⟩ :=
    exists_field_lift_open_or_closed sq.f₂₄ z hcomp (t ≫ d₁ ≫ sq.f₃₄)
  · right
    have ha₁ : a ≫ sq.f₂₄ = (t ≫ d₁) ≫ sq.f₃₄ := by simpa using ha
    have ha₂ : a ≫ sq.f₂₄ = (t ≫ d₂) ≫ sq.f₃₄ := by
      simpa only [Category.assoc, hD.w] using ha
    let b₁ := hpb.lift a (t ≫ d₁) ha₁
    let b₂ := hpb.lift a (t ≫ d₂) ha₂
    have hb : b₁ ≫ sq.f₁₂ = b₂ ≫ sq.f₁₂ := by
      exact (hpb.lift_fst _ _ _).trans (hpb.lift_fst _ _ _).symm
    refine ⟨hE.lift b₁ b₂ hb, hD.hom_ext ?_ ?_⟩
    · simp only [Category.assoc, he₁, IsPullback.lift_fst_assoc]
      exact hpb.lift_snd _ _ _
    · simp only [Category.assoc, he₂, IsPullback.lift_snd_assoc]
      exact hpb.lift_snd _ _ _
  · left
    have h : t ≫ d₁ = t ≫ d₂ :=
      eq_of_comp_eq_over_iso_complement sq.f₃₄ z (t ≫ d₁) (t ≫ d₂) c
        (by simpa using hc.symm)
        (by simpa only [Category.assoc, hD.w] using hc.symm)
    refine ⟨t ≫ d₁, hD.hom_ext ?_ ?_⟩
    · simp [Category.assoc, hd₁]
    · simpa only [Category.assoc, hd₂, Category.comp_id] using h

end AlgebraicGeometry.Scheme
