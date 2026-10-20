/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.CategoryTheory.Limits.Shapes.Pullback.CompLift
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.BaseChange.TwoLocalizations
public import Mathlib.AlgebraicGeometry.Limits

/-!
# Whole boundary factors through the same two-localization affine ambient

The source, coefficient maps, and two localization elements are the literal
ones in `TwoLocalizations`. The nested boundary is the exact pullback occurring
in `SourceTargetFullBoundaryAffineAmbients`. A Cartesian square transports
any supplied whole-scheme boundary factor into it, without replacing the
boundary by its support and without choosing any new geometric data.

Intended upstream module: `TwoLocalizationBoundaryFactors` in
`Aglib.AlgebraicGeometry.ProjectiveLine.BaseChange`.
Current consumer: the fixed-witness full-boundary standard-triple geometry
for the original relative affine-line normalization. The complete hypotheses
are explicit below; neither nonzero localization elements, finite maps,
flatness, affineness, closedness, nor nonempty sources are required here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.RelativeProjectiveLine.TwoLocalizations

variable (R : Type u) [CommRing R] (r : R) (s : Localization.Away r)
  {C B : Scheme.{u}} (F : C ⟶ ProjectiveSpace R (ULift.{u} (Fin 2))) (b : B ⟶ C)

/-- The first full-boundary map is precisely the supplier's canonical lift. -/
abbrev firstBoundaryMap : pullback (b ≫ F) (firstMap R r) ⟶ firstSource R r F :=
  pullback.lift (pullback.fst (b ≫ F) (firstMap R r) ≫ b)
    (pullback.snd (b ≫ F) (firstMap R r))
    (by simp [Category.assoc, pullback.condition])

/-- The literal nested whole-boundary pullback in the ambient supplier. -/
abbrev boundary := pullback (firstBoundaryMap R r F b) (sourceFirstMap R r s F)

/-- The displayed map from that boundary to the actual final source. -/
abbrev boundaryMap : boundary R r s F b ⟶ source R r s F := pullback.snd _ _

/-- The composite map from the nested boundary to its original full scheme. -/
abbrev boundaryOriginalMap : boundary R r s F b ⟶ B :=
  pullback.fst (firstBoundaryMap R r F b) (sourceFirstMap R r s F) ≫
    pullback.fst (b ≫ F) (firstMap R r)

/-- The nested boundary is Cartesian over the original whole boundary map. -/
theorem boundarySquare : IsPullback (boundaryOriginalMap R r s F b)
    (boundaryMap R r s F b) b (sourceMap R r s F) :=
  (IsPullback.of_hasPullback (firstBoundaryMap R r F b) (sourceFirstMap R r s F)).paste_horiz
    (pullback.isPullback_lift_comp b F (firstMap R r))

variable {E : Scheme.{u}} (e : E ⟶ C) (a : E ⟶ B) (ha : a ≫ b = e)

/-- Pull back a supplied factor through the unchanged whole boundary scheme. -/
def boundaryFactor : pullback e (sourceMap R r s F) ⟶ boundary R r s F b :=
  (boundarySquare R r s F b).lift
    (pullback.fst e (sourceMap R r s F) ≫ a)
    (pullback.snd e (sourceMap R r s F))
    (by rw [Category.assoc, ha, pullback.condition])

@[reassoc]
theorem boundaryFactor_map :
    boundaryFactor R r s F b e a ha ≫ boundaryMap R r s F b =
      pullback.snd e (sourceMap R r s F) := by
  simp only [boundaryFactor, IsPullback.lift_snd]

@[reassoc]
theorem boundaryFactor_original :
    boundaryFactor R r s F b e a ha ≫ boundaryOriginalMap R r s F b =
      pullback.fst e (sourceMap R r s F) ≫ a := by
  simp only [boundaryFactor, IsPullback.lift_fst]

/-- Both entire coproduct summands factor through the same supplied ambient.
For the fixed normalization data, take `d = d'` and `z = sO ≫ J`.
The domains are literally `D₂ = pullback d ρ` and `Z₂ = pullback z ρ`. -/
theorem coproductBoundary_factors_through_ambient
    {D Z : Scheme.{u}} (d : D ⟶ C) (z : Z ⟶ C)
    (U : (source R r s F).Opens)
    (u : boundary R r s F (coprod.desc d z) ⟶ U.toScheme)
    (hu : u ≫ U.ι = boundaryMap R r s F (coprod.desc d z)) :
    ∃ (d₂ : pullback d (sourceMap R r s F) ⟶ U.toScheme)
      (z₂ : pullback z (sourceMap R r s F) ⟶ U.toScheme),
      d₂ ≫ U.ι = pullback.snd d (sourceMap R r s F) ∧
      z₂ ≫ U.ι = pullback.snd z (sourceMap R r s F) := by
  refine ⟨boundaryFactor R r s F (coprod.desc d z) d coprod.inl
      (coprod.inl_desc d z) ≫ u,
    boundaryFactor R r s F (coprod.desc d z) z coprod.inr
      (coprod.inr_desc d z) ≫ u, ?_, ?_⟩
  · rw [Category.assoc, hu, boundaryFactor_map]
  · rw [Category.assoc, hu, boundaryFactor_map]

end AlgebraicGeometry.RelativeProjectiveLine.TwoLocalizations
