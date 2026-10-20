/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Dimension.FiberComponents
public import Motivic.Aglib.AlgebraicGeometry.Properties.Normal.OpenImmersion

/-!
# Geometry of the literal two-localization projective-line cover

The source and target are exactly the nested pullbacks used by the full-boundary
ambient supplier. Their projective and affine coefficient squares are proved by
pasting native pullbacks. The actual restriction is open and affine. Finiteness,
flatness and normal stalks are transported only from their stated original
suppliers; the native fiber-component theorem then applies without nonemptiness,
reducedness, positive rank or nonzero localization hypotheses.

Intended upstream module: `ProjectiveLine.BaseChange.TwoLocalizations` in `Aglib.AlgebraicGeometry`.
Current consumers: the same-witness relative affine-line normalization geometry
and the exact full-boundary ambient factorization. No comparison with a separately
chosen coefficient open or new compactification object is introduced. The full
scalar maps and complete hypotheses are in the declarations below.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.RelativeProjectiveLine.TwoLocalizations

variable (R : Type u) [CommRing R] (r : R) (s : Localization.Away r)

/-- The first actual projective coefficient map. -/
abbrev firstMap := ProjectiveSpace.map (algebraMap R (Localization.Away r))
  (ULift.{u} (Fin 2))

/-- The second actual projective coefficient map. -/
abbrev secondMap := ProjectiveSpace.map
  (algebraMap (Localization.Away r) (Localization.Away s)) (ULift.{u} (Fin 2))

/-- The composite projective coefficient map, without changing its scalar maps. -/
abbrev projectiveBaseMap := secondMap R r s ≫ firstMap R r

/-- The literal composite of the two localization maps on affine bases. -/
abbrev baseMap : Spec (.of (Localization.Away s)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away r) (Localization.Away s))) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))

/-- The supplier's literal target pullback, not a replacement projective line. -/
abbrev target := pullback (𝟙 (ProjectiveSpace (Localization.Away r)
  (ULift.{u} (Fin 2)))) (secondMap R r s)

/-- The target's projection to the first projective line. -/
abbrev targetMap : target R r s ⟶ ProjectiveSpace (Localization.Away r)
    (ULift.{u} (Fin 2)) := pullback.fst _ _

/-- The canonical identity-pullback projection to the final projective line. -/
abbrev targetIsoMap : target R r s ⟶ ProjectiveSpace (Localization.Away s)
    (ULift.{u} (Fin 2)) := pullback.snd _ _

instance targetIsoMap_isIso : IsIso (targetIsoMap R r s) := by
  dsimp only [targetIsoMap]
  infer_instance

@[reassoc (attr := simp)]
theorem targetIsoMap_secondMap : targetIsoMap R r s ≫ secondMap R r s =
    targetMap R r s := by
  simpa only [Category.comp_id] using
    (pullback.condition (f := 𝟙 (ProjectiveSpace (Localization.Away r)
      (ULift.{u} (Fin 2)))) (g := secondMap R r s)).symm

variable {C : Scheme.{u}} (F : C ⟶ ProjectiveSpace R (ULift.{u} (Fin 2)))

/-- The first literal source pullback. -/
abbrev firstSource := pullback F (firstMap R r)

/-- Its coordinate projection to the first localized projective line. -/
abbrev firstProjection : firstSource R r F ⟶
    ProjectiveSpace (Localization.Away r) (ULift.{u} (Fin 2)) := pullback.snd _ _

/-- The supplier's literal nested source pullback. -/
abbrev source := pullback (firstProjection R r F) (targetMap R r s)

/-- The second restriction map to the first source pullback. -/
abbrev sourceFirstMap : source R r s F ⟶ firstSource R r F := pullback.fst _ _

/-- The second coordinate projection to the literal target pullback. -/
abbrev sourceTargetMap : source R r s F ⟶ target R r s := pullback.snd _ _

/-- The composite restriction to the unchanged original source. -/
abbrev sourceMap : source R r s F ⟶ C :=
  sourceFirstMap R r s F ≫ pullback.fst F (firstMap R r)

/-- The finite-cover coordinate map to the final projective line. -/
abbrev toProjectiveLine : source R r s F ⟶
    ProjectiveSpace (Localization.Away s) (ULift.{u} (Fin 2)) :=
  sourceTargetMap R r s F ≫ targetIsoMap R r s

/-- The structural projection of the literal final source. -/
abbrev projection : source R r s F ⟶ Spec (.of (Localization.Away s)) :=
  toProjectiveLine R r s F ≫ ProjectiveSpace.toSpec (Localization.Away s)
    (ULift.{u} (Fin 2))

/-- The nested native pullbacks paste to the original projective coefficient square. -/
theorem projectiveSquare : IsPullback (sourceMap R r s F)
    (toProjectiveLine R r s F) F (projectiveBaseMap R r s) := by
  have H : IsPullback (sourceFirstMap R r s F) (toProjectiveLine R r s F)
      (firstProjection R r F) (secondMap R r s) := by
    simpa only [Category.comp_id] using
      (IsPullback.of_hasPullback (firstProjection R r F) (targetMap R r s)).paste_vert
        (IsPullback.of_hasPullback
          (𝟙 (ProjectiveSpace (Localization.Away r) (ULift.{u} (Fin 2))))
          (secondMap R r s))
  exact H.paste_horiz (IsPullback.of_hasPullback F (firstMap R r))

@[reassoc]
theorem sourceMap_toProjectiveLine : sourceMap R r s F ≫ F =
    toProjectiveLine R r s F ≫ projectiveBaseMap R r s :=
  (projectiveSquare R r s F).w

/-- The same square over the literal composite affine coefficient map. -/
theorem baseSquare : IsPullback (sourceMap R r s F) (projection R r s F)
    (F ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) (baseMap R r s) :=
  (projectiveSquare R r s F).paste_vert
    ((ProjectiveSpace.isPullback_map
      (algebraMap (Localization.Away r) (Localization.Away s))
      (ULift.{u} (Fin 2))).paste_horiz
      (ProjectiveSpace.isPullback_map (algebraMap R (Localization.Away r))
        (ULift.{u} (Fin 2))))

@[reassoc]
theorem sourceMap_projection : sourceMap R r s F ≫
    (F ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) =
      projection R r s F ≫ baseMap R r s :=
  (baseSquare R r s F).w

instance baseMap_isOpenImmersion : IsOpenImmersion (baseMap R r s) := by
  dsimp only [baseMap]
  infer_instance

instance sourceMap_isOpenImmersion : IsOpenImmersion (sourceMap R r s F) :=
  MorphismProperty.of_isPullback (baseSquare R r s F).flip inferInstance

instance sourceMap_isAffineHom : IsAffineHom (sourceMap R r s F) :=
  MorphismProperty.of_isPullback (baseSquare R r s F).flip inferInstance

instance toProjectiveLine_isFinite [IsFinite F] : IsFinite (toProjectiveLine R r s F) :=
  MorphismProperty.of_isPullback (projectiveSquare R r s F) inferInstance

instance toProjectiveLine_flat [Flat F] : Flat (toProjectiveLine R r s F) :=
  MorphismProperty.of_isPullback (projectiveSquare R r s F) inferInstance

instance projection_isProper [IsFinite F] : IsProper (projection R r s F) := by
  dsimp only [projection]
  infer_instance

/-- Total-space normality is transported along the actual open restriction. -/
theorem normalStalks (hC : Scheme.NormalStalks C) :
    Scheme.NormalStalks (source R r s F) :=
  hC.of_isOpenImmersion (sourceMap R r s F)

/-- Every component of each literal final structural fiber has dimension one. -/
theorem fiber_component_dimension [IsFinite F] [Flat F]
    (x : Spec (.of (Localization.Away s)))
    {Z : Set ((projection R r s F).fiber x)}
    (hZ : Z ∈ irreducibleComponents ((projection R r s F).fiber x)) :
    topologicalKrullDim Z = 1 := by
  exact RelativeProjectiveLine.topologicalKrullDim_eq_one_of_mem_nativeFiberComponents
    (Localization.Away s) (projection R r s F) (toProjectiveLine R r s F)
    (Iso.refl _) (by simp only [Iso.refl_hom, Category.comp_id]) x hZ

end AlgebraicGeometry.RelativeProjectiveLine.TwoLocalizations

