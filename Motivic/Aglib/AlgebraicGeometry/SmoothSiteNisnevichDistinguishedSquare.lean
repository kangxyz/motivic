/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.NisnevichDistinguishedSquare
public import Motivic.AlgebraicGeometry.SmoothSiteNisnevich

/-!
# Distinguished-square descent on the actual smooth Nisnevich site

An open immersion and an étale neighborhood which is an isomorphism over its
closed complement give a sheaf pullback square. Both the covering family and
the diagonal cover of the right self-overlap are proved from field-valued
lifting. Only the étale pullbacks which exist in the smooth site are used.
The coefficient category is arbitrary, including universe-lifted abelian groups.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w

namespace Motivic.SmoothSite

variable {S : Scheme.{u}}

/-- Two étale arrows which jointly lift field-valued points generate a smooth
Nisnevich covering sieve. The lifts are scheme maps, not hypothetical smooth
objects representing arbitrary field extensions. -/
theorem ofTwoArrows_mem_nisnevichTopology_of_field_lifting
    {U V X : SmoothSite S} (i : U ⟶ X) (p : V ⟶ X)
    [Etale i.left] [Etale p.left]
    (hlift : ∀ (K : Type u) [Field K] (x : Spec (.of K) ⟶ X.left),
      (∃ a : Spec (.of K) ⟶ U.left, a ≫ i.left = x) ∨
        (∃ b : Spec (.of K) ⟶ V.left, b ≫ p.left = x)) :
    Sieve.ofTwoArrows i p ∈ nisnevichTopology S X := by
  let f : ∀ j, pairFunction U V j ⟶ X := fun j ↦ WalkingPair.casesOn j i p
  apply mem_nisnevichTopology_iff.mpr
  refine ⟨Presieve.ofArrows _ f, ?_, Sieve.le_generate _⟩
  rw [mem_nisnevichPrecoverage_iff, Presieve.map_ofArrows]
  change Presieve.ofArrows (fun j ↦ (pairFunction U V j).left)
    (fun j ↦ (f j).left) ∈ Nisnevich.precoverage X.left
  rw [Nisnevich.mem_precoverage_iff]
  refine ⟨?_, Nisnevich.isResidueFieldLifting_of_mem ?_⟩
  · rintro _ _ ⟨j⟩
    cases j <;> assumption
  · rw [Nisnevich.mem_fieldLiftingPrecoverage_iff]
    intro K _ x
    obtain ⟨a, ha⟩ | ⟨b, hb⟩ := hlift K x
    · exact ⟨U.left, i.left, ⟨WalkingPair.left⟩, a, ha⟩
    · exact ⟨V.left, p.left, ⟨WalkingPair.right⟩, b, hb⟩

/-- The two original arrows of a Nisnevich distinguished square cover its base. -/
theorem ofTwoArrows_mem_nisnevichTopology_of_iso_complement
    {U V X : SmoothSite S} (i : U ⟶ X) (p : V ⟶ X)
    [IsOpenImmersion i.left] [Etale p.left]
    {Z : Scheme.{u}} (z : Z ⟶ X.left) [IsClosedImmersion z]
    (hcomp : Set.range z = (Set.range i.left)ᶜ)
    [IsIso (pullback.snd p.left z)] :
    Sieve.ofTwoArrows i p ∈ nisnevichTopology S X :=
  ofTwoArrows_mem_nisnevichTopology_of_field_lifting i p
    (fun _ _ x ↦ Scheme.exists_field_lift_open_or_etale i.left p.left z hcomp x)

set_option backward.isDefEq.respectTransparency false in
/-- Every ordinary sheaf on the actual smooth Nisnevich site takes a geometric
Nisnevich distinguished square to a pullback. No monicity of the étale arrow
or additional sheaf-gluing hypothesis is imposed. -/
theorem isPullback_op_map_of_iso_complement
    (sq : Square (SmoothSite S)) (hpb : sq.IsPullback)
    [IsOpenImmersion sq.f₂₄.left] [Etale sq.f₃₄.left]
    {Z : Scheme.{u}} (z : Z ⟶ sq.X₄.left) [IsClosedImmersion z]
    (hcomp : Set.range z = (Set.range sq.f₂₄.left)ᶜ)
    [IsIso (pullback.snd sq.f₃₄.left z)]
    {A : Type v} [Category.{w} A] (F : Sheaf (nisnevichTopology S) A) :
    (sq.op.map F.obj).IsPullback := by
  have hpb' : IsPullback sq.f₁₂.left sq.f₁₃.left sq.f₂₄.left sq.f₃₄.left :=
    (forgetScheme S).map_isPullback hpb
  have : Etale sq.f₁₂.left := MorphismProperty.of_isPullback hpb'.flip inferInstance
  have : Etale sq.f₁₃.left := MorphismProperty.of_isPullback hpb' inferInstance
  have : Mono sq.f₂₄ := (forgetScheme S).mono_of_mono_map (by
    change Mono sq.f₂₄.left
    infer_instance)
  let d₁ := (pullback.fst sq.f₃₄ sq.f₃₄).left
  let d₂ := (pullback.snd sq.f₃₄ sq.f₃₄).left
  let e₁ := (pullback.fst sq.f₁₂ sq.f₁₂).left
  let e₂ := (pullback.snd sq.f₁₂ sq.f₁₂).left
  have hD : IsPullback d₁ d₂ sq.f₃₄.left sq.f₃₄.left :=
    (forgetScheme S).map_isPullback (IsPullback.of_hasPullback _ _)
  have hE : IsPullback e₁ e₂ sq.f₁₂.left sq.f₁₂.left :=
    (forgetScheme S).map_isPullback (IsPullback.of_hasPullback _ _)
  let d := (pullback.diagonal sq.f₃₄).left
  let e := sq.overlapMap.left
  have hd₁ : d ≫ d₁ = 𝟙 _ := by
    exact congrArg (fun f ↦ f.left) (pullback.diagonal_fst sq.f₃₄)
  have hd₂ : d ≫ d₂ = 𝟙 _ := by
    exact congrArg (fun f ↦ f.left) (pullback.diagonal_snd sq.f₃₄)
  have he₁ : e ≫ d₁ = e₁ ≫ sq.f₁₃.left := by
    exact congrArg (fun f ↦ f.left) sq.overlapMap_fst
  have he₂ : e ≫ d₂ = e₂ ≫ sq.f₁₃.left := by
    exact congrArg (fun f ↦ f.left) sq.overlapMap_snd
  have : Etale d₁ := MorphismProperty.of_isPullback hD.flip inferInstance
  have : Etale e₁ := MorphismProperty.of_isPullback hE.flip inferInstance
  have : Etale (d ≫ d₁) := by rw [hd₁]; infer_instance
  have : Etale d := Etale.of_comp d d₁
  have : Etale (e ≫ d₁) := by rw [he₁]; infer_instance
  have : Etale e := Etale.of_comp e d₁
  apply sq.isPullback_op_map_of_diagonal_cover hpb
    (ofTwoArrows_mem_nisnevichTopology_of_iso_complement sq.f₂₄ sq.f₃₄ z hcomp) _ F
  apply ofTwoArrows_mem_nisnevichTopology_of_field_lifting
  intro K _ t
  have : IsOpenImmersion (sq.map (forgetScheme S)).f₂₄ := by
    change IsOpenImmersion sq.f₂₄.left
    infer_instance
  have : IsIso (pullback.snd (sq.map (forgetScheme S)).f₃₄ z) := by
    change IsIso (pullback.snd sq.f₃₄.left z)
    infer_instance
  exact Scheme.exists_field_lift_diagonal_or_overlap (sq.map (forgetScheme S))
    hpb' z hcomp d₁ d₂ hD e₁ e₂ hE d hd₁ hd₂ e he₁ he₂ t

end Motivic.SmoothSite
