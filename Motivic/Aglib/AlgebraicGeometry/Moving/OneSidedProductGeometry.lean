/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.FactorBoundaryGeometry
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.RetainedGraph
/-! # Original target and good target in the one-sided parameter product

The parameter open is not substituted for the retained target. The actual graph
of its map into the original target supplies the zero endpoint.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.RelativeCurvePencil
universe u
namespace AlgebraicGeometry.Scheme.Moving
variable {S C Y X V Z D : Scheme.{u}} (π : C ⟶ S) (j : Y ⟶ C)
  (x : X ⟶ C) (v : V ⟶ X) (r : Y ⟶ X) (hr : r ≫ x = j)

def parameterGraph : Y ⟶ retainedProduct (j ≫ π) π x :=
  pullback.lift (𝟙 Y) r (by simp only [Category.id_comp, ← Category.assoc, hr])

@[reassoc (attr := simp)] theorem parameterGraph_fst :
    parameterGraph π j x r hr ≫ pullback.fst _ _ = 𝟙 Y := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem parameterGraph_snd :
    parameterGraph π j x r hr ≫ pullback.snd _ _ = r := pullback.lift_snd _ _ _

theorem parameterGraph_inclusion :
    parameterGraph π j x r hr ≫ retainedProductInclusion (j ≫ π) π x =
      Hom.compactificationGraph π j := by
  apply pullback.hom_ext <;> simp [Hom.compactificationGraph, hr]

/-- The larger retained target is covered using only infinity. -/
theorem product_missing_cover (d : D ⟶ C)
    (h : ∀ c : C, c ∈ Set.range x ∨ c ∈ Set.range d) :
    ∀ a : (pullback (j ≫ π) π : Scheme),
      a ∈ Set.range (retainedProductInclusion (j ≫ π) π x) ∨
        a ∈ Set.range (Hom.infinityProductMap π j d) := by
  intro a
  rcases h ((pullback.snd (j ≫ π) π) a) with ⟨b, hb⟩ | hd
  · obtain ⟨t, _, ht⟩ := Scheme.exists_preimage_of_isPullback
      (retainedProductInclusion_isPullback (j ≫ π) π x) b a hb
    exact Or.inl ⟨t, ht⟩
  · right
    change a ∈ Set.range (pullback.fst (pullback.snd (j ≫ π) π) d)
    rw [Scheme.Pullback.range_fst]
    exact hd

/-- Both endpoint divisors use the smaller good target and the full bad boundary. -/
theorem product_good_cover (s : Z ⟶ Y) (d : D ⟶ C)
    (h : ∀ c : C, c ∈ Set.range (v ≫ x) ∨
      c ∈ Set.range d ∨ c ∈ Set.range (s ≫ j)) :
    ∀ a : (pullback (j ≫ π) π : Scheme),
      a ∈ Set.range (retainedProductInclusion (j ≫ π) (x ≫ π) v ≫
        retainedProductInclusion (j ≫ π) π x) ∨
      a ∈ Set.range (Hom.fullBoundaryProductMap π j d s) := by
  intro a
  rcases lambdaBoundary_retained_cover π j s d (v ≫ x) h a with ha | ha
  · obtain ⟨b, hb⟩ := ha
    have hs : (pullback.snd (j ≫ π) π) a ∈ Set.range (v ≫ x) := by
      rw [← hb]
      exact ⟨(pullback.snd (j ≫ π) ((v ≫ x) ≫ π)) b,
        congrArg (fun f => f b) (retainedProductInclusion_snd (j ≫ π) π (v ≫ x)).symm⟩
    obtain ⟨c, hc⟩ := hs
    obtain ⟨b, hb, hba⟩ := Scheme.exists_preimage_of_isPullback
      (retainedProductInclusion_isPullback (j ≫ π) π x) (v c) a hc
    obtain ⟨t, _, ht⟩ := Scheme.exists_preimage_of_isPullback
      (retainedProductInclusion_isPullback (j ≫ π) (x ≫ π) v) c b hb.symm
    exact Or.inl ⟨t, by simpa only [Scheme.Hom.comp_apply, ht] using hba⟩
  · exact Or.inr ha

end AlgebraicGeometry.Scheme.Moving
