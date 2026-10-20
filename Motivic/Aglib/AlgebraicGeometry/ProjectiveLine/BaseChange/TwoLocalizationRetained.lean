/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.BaseChange.TwoLocalizations
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# The retained curve on the literal two-localization source

The retained scheme is the native pullback of the original retained map along
`TwoLocalizations.sourceMap`. Its structural square is proved by pasting the
native pullback with `baseSquare`. Relative smoothness is transported only from
the original retained curve. Quasi-affineness uses the affine projection to that
curve, so quasi-compactness is retained rather than inferred for an arbitrary open.
Smoothness of the new coefficient base still requires the original smooth map.

Intended upstream module: `ProjectiveLine.BaseChange.TwoLocalizationRetained` in
`Aglib.AlgebraicGeometry`. Current consumers: the actual normalization retained
geometry and the marked-product frame base-change. The full hypotheses and
literal maps appear below; no finiteness, flatness, nonemptiness, nonzero
localization or new geometric choice is needed for this transport leaf.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.RelativeProjectiveLine.TwoLocalizations

variable (R : Type u) [CommRing R] (r : R) (s : Localization.Away r)
  {C Y : Scheme.{u}} (F : C ⟶ ProjectiveSpace R (ULift.{u} (Fin 2))) (j : Y ⟶ C)

/-- The original retained scheme restricted along the literal final source map. -/
abbrev retainedSource := pullback j (sourceMap R r s F)

/-- The actual retained inclusion into the unchanged nested compactification. -/
abbrev retainedInclusion : retainedSource R r s F j ⟶ source R r s F :=
  pullback.snd _ _

/-- The affine projection to the original retained scheme. -/
abbrev retainedSourceMap : retainedSource R r s F j ⟶ Y := pullback.fst _ _

/-- The retained curve's literal structural map on the final coefficient base. -/
abbrev retainedProjection : retainedSource R r s F j ⟶
    Spec (.of (Localization.Away s)) := retainedInclusion R r s F j ≫ projection R r s F

/-- The retained structural map is the actual base change of the original one. -/
theorem retainedBaseSquare : IsPullback (retainedSourceMap R r s F j)
    (retainedProjection R r s F j)
    (j ≫ (F ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))) (baseMap R r s) :=
  (IsPullback.of_hasPullback j (sourceMap R r s F)).paste_vert (baseSquare R r s F)

@[reassoc]
theorem retainedSourceMap_projection : retainedSourceMap R r s F j ≫
    (j ≫ (F ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))) =
      retainedProjection R r s F j ≫ baseMap R r s :=
  (retainedBaseSquare R r s F j).w

instance retainedInclusion_isOpenImmersion [IsOpenImmersion j] :
    IsOpenImmersion (retainedInclusion R r s F j) := by
  dsimp only [retainedInclusion]
  infer_instance

instance retainedSourceMap_isAffineHom : IsAffineHom (retainedSourceMap R r s F j) :=
  MorphismProperty.of_isPullback
    (IsPullback.of_hasPullback j (sourceMap R r s F)).flip
    (sourceMap_isAffineHom R r s F)

instance retainedSourceMap_isOpenImmersion :
    IsOpenImmersion (retainedSourceMap R r s F j) := by
  dsimp only [retainedSourceMap]
  infer_instance

/-- Smooth relative dimension is transported only from the retained curve. -/
instance retainedProjection_smooth
    [SmoothOfRelativeDimension 1 (j ≫ (F ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))))] :
    SmoothOfRelativeDimension 1 (retainedProjection R r s F j) :=
  MorphismProperty.of_isPullback (retainedBaseSquare R r s F j) inferInstance

/-- Affine base change preserves quasi-affineness, including quasi-compactness. -/
theorem retainedSource_quasiAffine [Y.IsQuasiAffine] :
    (retainedSource R r s F j).IsQuasiAffine :=
  Scheme.IsQuasiAffine.of_isAffineHom (retainedSourceMap R r s F j)

/-- Base smoothness comes from the original supplied map and the open restriction. -/
instance baseMap_comp_smooth {T : Scheme.{u}} (t : Spec (.of R) ⟶ T) [Smooth t] :
    Smooth (baseMap R r s ≫ t) := by
  infer_instance

end AlgebraicGeometry.RelativeProjectiveLine.TwoLocalizations

