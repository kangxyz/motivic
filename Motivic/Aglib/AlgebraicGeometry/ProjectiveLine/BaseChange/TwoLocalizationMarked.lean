/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.BaseChange.TwoLocalizationRetained
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.GraphBoundaryRestriction

/-!
# The whole marked scheme on the literal twice-localized retained curve

The marked scheme is the direct pullback of the original marked inclusion along
`sourceMap`. The literal retained and marked product has its two original
projection equations. Its Cartesian square makes its map to the original
product open, hence flat. The restricted marked graph square follows from that
same square, retaining the entire marked scheme including nilpotents.

Intended upstream module:
`Aglib.AlgebraicGeometry.ProjectiveLine.BaseChange.TwoLocalizationMarked`.
Current consumer: the preserved marked ideal and positive divisor frames in
`Modules.Invertible.Frames.RelativeCurve.TwoLocalizationMarked`.
No nonzero-localization, nonempty-source, reducedness, smoothness, or finiteness
premise is used by these product comparisons. All maps are displayed below.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme Scheme.Hom

universe u

namespace AlgebraicGeometry.RelativeProjectiveLine.TwoLocalizations

variable (R : Type u) [CommRing R] (r : R) (s : Localization.Away r)
  {C Y Z : Scheme.{u}} (F : C ⟶ ProjectiveSpace R (ULift.{u} (Fin 2)))
  (j : Y ⟶ C) (z : Z ⟶ Y)

/-- The whole original marked scheme, pulled back directly along the source restriction. -/
abbrev markedSource := pullback (z ≫ j) (sourceMap R r s F)

/-- The second pullback projection to the twice-localized source. -/
abbrev markedInclusion : markedSource R r s F j z ⟶ source R r s F :=
  pullback.snd _ _

/-- The first pullback projection to the whole original marked scheme `Z`. -/
abbrev markedSourceMap : markedSource R r s F j z ⟶ Z := pullback.fst _ _

/-- The induced marking of the literal retained pullback. -/
def markedLift : markedSource R r s F j z ⟶ retainedSource R r s F j :=
  pullback.lift (markedSourceMap R r s F j z ≫ z) (markedInclusion R r s F j z)
    (by simpa only [Category.assoc] using
      pullback.condition (f := z ≫ j) (g := sourceMap R r s F))

@[reassoc (attr := simp)]
theorem markedLift_sourceMap :
    markedLift R r s F j z ≫ retainedSourceMap R r s F j =
      markedSourceMap R r s F j z ≫ z :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem markedLift_inclusion :
    markedLift R r s F j z ≫ retainedInclusion R r s F j =
      markedInclusion R r s F j z :=
  pullback.lift_snd _ _ _

local notation "q₀" => F ≫ ProjectiveSpace.toSpec R (ULift (Fin 2))
local notation "q₂" => projection R r s F
local notation "j₂" => retainedInclusion R r s F j
local notation "yρ" => retainedSourceMap R r s F j
local notation "zρ" => markedSourceMap R r s F j z
local notation "s₂" => markedLift R r s F j z
local notation "M₀" => pullback (j ≫ q₀) (z ≫ j ≫ q₀)
local notation "M₂" => pullback (j₂ ≫ q₂) (s₂ ≫ j₂ ≫ q₂)

@[reassoc]
theorem markedSourceMap_projection :
    zρ ≫ (z ≫ j ≫ q₀) = (s₂ ≫ j₂ ≫ q₂) ≫ baseMap R r s := by
  have H := (IsPullback.of_hasPullback (z ≫ j) (sourceMap R r s F)).paste_vert
    (baseSquare R r s F)
  simpa only [Category.assoc, markedLift_inclusion_assoc] using H.w

/-- The actual marked-product map, retaining both original projections. -/
def markedProductMap : M₂ ⟶ M₀ :=
  pullback.lift (pullback.fst _ _ ≫ yρ) (pullback.snd _ _ ≫ zρ) (by
    calc
      (pullback.fst (j₂ ≫ q₂) (s₂ ≫ j₂ ≫ q₂) ≫ yρ) ≫ (j ≫ q₀) =
          (pullback.fst (j₂ ≫ q₂) (s₂ ≫ j₂ ≫ q₂) ≫ (j₂ ≫ q₂)) ≫ baseMap R r s := by
        simpa only [Category.assoc] using congrArg
          (fun k => pullback.fst (j₂ ≫ q₂) (s₂ ≫ j₂ ≫ q₂) ≫ k)
          (retainedSourceMap_projection R r s F j)
      _ = (pullback.snd (j₂ ≫ q₂) (s₂ ≫ j₂ ≫ q₂) ≫
          (s₂ ≫ j₂ ≫ q₂)) ≫ baseMap R r s :=
        congrArg (fun k => k ≫ baseMap R r s)
          (pullback.condition (f := j₂ ≫ q₂) (g := s₂ ≫ j₂ ≫ q₂))
      _ = (pullback.snd (j₂ ≫ q₂) (s₂ ≫ j₂ ≫ q₂) ≫ zρ) ≫ (z ≫ j ≫ q₀) := by
        simpa only [Category.assoc] using congrArg
          (fun k => pullback.snd (j₂ ≫ q₂) (s₂ ≫ j₂ ≫ q₂) ≫ k)
          (markedSourceMap_projection R r s F j z).symm)

@[reassoc (attr := simp)]
theorem markedProductMap_fst :
    markedProductMap R r s F j z ≫ pullback.fst (j ≫ q₀) (z ≫ j ≫ q₀) =
      pullback.fst (j₂ ≫ q₂) (s₂ ≫ j₂ ≫ q₂) ≫ yρ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem markedProductMap_snd :
    markedProductMap R r s F j z ≫ pullback.snd (j ≫ q₀) (z ≫ j ≫ q₀) =
      pullback.snd (j₂ ≫ q₂) (s₂ ≫ j₂ ≫ q₂) ≫ zρ :=
  pullback.lift_snd _ _ _

/-- The product map is the actual base change of the whole marked restriction. -/
theorem markedProductSquare :
    IsPullback (markedProductMap R r s F j z)
      (pullback.snd (j₂ ≫ q₂) (s₂ ≫ j₂ ≫ q₂))
      (pullback.snd (j ≫ q₀) (z ≫ j ≫ q₀)) zρ := by
  have H : IsPullback
      (pullback.fst (j₂ ≫ q₂) (s₂ ≫ j₂ ≫ q₂) ≫ yρ)
      (pullback.snd (j₂ ≫ q₂) (s₂ ≫ j₂ ≫ q₂))
      (j ≫ q₀) (zρ ≫ (z ≫ j ≫ q₀)) := by
    simpa only [← markedSourceMap_projection] using
      (IsPullback.of_hasPullback (j₂ ≫ q₂) (s₂ ≫ j₂ ≫ q₂)).paste_horiz
        (retainedBaseSquare R r s F j)
  have H' : IsPullback
      (markedProductMap R r s F j z ≫ pullback.fst (j ≫ q₀) (z ≫ j ≫ q₀))
      (pullback.snd (j₂ ≫ q₂) (s₂ ≫ j₂ ≫ q₂))
      (j ≫ q₀) (zρ ≫ (z ≫ j ≫ q₀)) := by
    simpa only [markedProductMap_fst] using H
  exact H'.of_right (markedProductMap_snd R r s F j z)
    (IsPullback.of_hasPullback (j ≫ q₀) (z ≫ j ≫ q₀))

instance markedProductMap_isOpenImmersion : IsOpenImmersion (markedProductMap R r s F j z) :=
  MorphismProperty.of_isPullback (markedProductSquare R r s F j z).flip inferInstance

@[reassoc]
theorem markedGraph_comm :
    zρ ≫ restrictedBoundaryGraph q₀ j z =
      restrictedBoundaryGraph q₂ j₂ s₂ ≫ markedProductMap R r s F j z := by
  apply pullback.hom_ext <;>
    simp [restrictedBoundaryGraph, Category.assoc]

/-- Cancel the product square against the two graph-to-marked projection identities. -/
theorem markedGraphSquare :
    IsPullback zρ (restrictedBoundaryGraph q₂ j₂ s₂)
      (restrictedBoundaryGraph q₀ j z) (markedProductMap R r s F j z) := by
  have H : IsPullback zρ
      (restrictedBoundaryGraph q₂ j₂ s₂ ≫
        pullback.snd (j₂ ≫ q₂) (s₂ ≫ j₂ ≫ q₂))
      (restrictedBoundaryGraph q₀ j z ≫ pullback.snd (j ≫ q₀) (z ≫ j ≫ q₀)) zρ := by
    simp only [restrictedBoundaryGraph, pullback.lift_snd]
    exact IsPullback.of_vert_isIso ⟨by simp⟩
  exact H.of_bot (markedGraph_comm R r s F j z)
    (markedProductSquare R r s F j z)

/-- The whole direct boundary remains disjoint from the whole retained open. -/
theorem retainedBoundary_disjoint {D : Scheme.{u}} (d : D ⟶ C)
    (hd : Disjoint (Set.range j) (Set.range d)) :
    Disjoint (Set.range j₂) (Set.range (pullback.snd d (sourceMap R r s F))) := by
  dsimp only [retainedInclusion]
  rw [Scheme.Pullback.range_snd, Scheme.Pullback.range_snd]
  exact Disjoint.preimage (sourceMap R r s F) hd

end AlgebraicGeometry.RelativeProjectiveLine.TwoLocalizations
