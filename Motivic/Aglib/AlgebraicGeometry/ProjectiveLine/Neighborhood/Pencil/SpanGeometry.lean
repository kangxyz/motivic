module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Pencil.Sites
/-! # The literal original source spans used by the relative correcting pencil -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (k R : Type u) [Field k] [CommRing R]
  (b : Spec (.of R) ⟶ Spec (.of k)) [Smooth b]
  (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme] (r : R)

abbrev neighborhoodLambdaCurve :=
  (neighborhoodRetainedInclusion R V ⁻¹ᵁ neighborhoodSectionOpen R V r).toScheme
abbrev neighborhoodLambdaSourceMap :=
  (neighborhoodRetainedInclusion R V ∣_ neighborhoodSectionOpen R V r) ≫
    commonNeighborhoodSectionProjection R V r
abbrev neighborhoodLambdaTargetMap :=
  (neighborhoodRetainedInclusion R V ⁻¹ᵁ neighborhoodSectionOpen R V r).ι ≫
    pullback.snd (neighborhoodProjection R V)
      ((neighborhoodRetainedOpen R V).ι ≫ ProjectiveSpace.toSpec R _)
abbrev neighborhoodPsiSourceMap := pullback.fst (fixedPsiProjection R r)
  ((neighborhoodRetainedOpen R V).ι ≫ ProjectiveSpace.toSpec R _)
abbrev neighborhoodPsiTargetMap := pullback.snd (fixedPsiProjection R r)
  ((neighborhoodRetainedOpen R V).ι ≫ ProjectiveSpace.toSpec R _)
abbrev neighborhoodCommonSourceMap := pullback.fst (commonNeighborhoodProjection R V r)
  ((neighborhoodRetainedOpen R V).ι ≫ ProjectiveSpace.toSpec R _)
abbrev neighborhoodCommonTargetMap := pullback.snd (commonNeighborhoodProjection R V r)
  ((neighborhoodRetainedOpen R V).ι ≫ ProjectiveSpace.toSpec R _)

lemma neighborhoodLambdaCurve_affine : IsAffine (neighborhoodLambdaCurve R V r) := by
  dsimp only [neighborhoodLambdaCurve, neighborhoodSectionOpen]
  rw [neighborhoodSerreOpen_eq_compact]
  exact neighborhoodRestrictedRetained_affine R V r

@[reassoc] lemma neighborhoodLambdaSourceMap_base :
    neighborhoodLambdaSourceMap R V r ≫
      ((neighborhoodSourceOpen R V r).ι ≫ neighborhoodProjection R V) =
    (neighborhoodRetainedInclusion R V ⁻¹ᵁ neighborhoodSectionOpen R V r).ι ≫
      pullback.fst (neighborhoodProjection R V)
        ((neighborhoodRetainedOpen R V).ι ≫ ProjectiveSpace.toSpec R _) ≫
          neighborhoodProjection R V := by
  simp only [neighborhoodLambdaSourceMap, commonNeighborhoodSectionProjection,
    neighborhoodRestrictedProjection, Category.assoc,
    Scheme.isoOfEq_hom_ι_assoc, morphismRestrict_ι_assoc,
    neighborhoodRetainedInclusion_fst_assoc]

lemma neighborhoodLambda_base :
    neighborhoodLambdaSourceMap R V r ≫ (neighborhoodLambdaSite k R b V r).hom =
      neighborhoodLambdaTargetMap R V r ≫ (neighborhoodTargetSite k R b V).hom := by
  change neighborhoodLambdaSourceMap R V r ≫
    (((neighborhoodSourceOpen R V r).ι ≫ neighborhoodProjection R V) ≫ b) = _
  rw [← Category.assoc, neighborhoodLambdaSourceMap_base]
  exact congrArg (fun f =>
    (neighborhoodRetainedInclusion R V ⁻¹ᵁ neighborhoodSectionOpen R V r).ι ≫ f)
      (pullback.condition_assoc b)

lemma neighborhoodPsi_base :
    neighborhoodPsiSourceMap R V r ≫ (neighborhoodPsiSite k R b r).hom =
      neighborhoodPsiTargetMap R V r ≫ (neighborhoodTargetSite k R b V).hom := by
  exact pullback.condition_assoc b

lemma neighborhoodCommon_base :
    neighborhoodCommonSourceMap R V r ≫ (neighborhoodCommonSite k R b V r).hom =
      neighborhoodCommonTargetMap R V r ≫ (neighborhoodTargetSite k R b V).hom := by
  exact pullback.condition_assoc b

lemma neighborhoodLambda_total_smooth :
    Smooth (neighborhoodLambdaSourceMap R V r ≫ (neighborhoodLambdaSite k R b V r).hom) := by
  change Smooth (neighborhoodLambdaSourceMap R V r ≫
    (((neighborhoodSourceOpen R V r).ι ≫ neighborhoodProjection R V) ≫ b))
  rw [← Category.assoc, neighborhoodLambdaSourceMap_base]
  have := neighborhoodRetainedCurve_smooth R V
  have : Smooth (pullback.fst (neighborhoodProjection R V)
      ((neighborhoodRetainedOpen R V).ι ≫ ProjectiveSpace.toSpec R _)) := by
    have h := neighborhoodRetainedCurve_smooth R V
    rw [neighborhoodRetainedInclusion_fst] at h
    exact SmoothOfRelativeDimension.smooth 1 _
  have : Smooth (neighborhoodProjection R V ≫ b) := by
    simpa only [neighborhoodProjection, neighborhoodInclusion, Category.assoc,
      chart_toSpec, Scheme.Hom.boundaryLineProjection] using
      neighborhood_open_line_smooth k R b V.ι
  rw [Category.assoc, Category.assoc]
  infer_instance

omit [IsAffine V.toScheme] in
lemma neighborhoodPsi_total_smooth :
    Smooth (neighborhoodPsiSourceMap R V r ≫ (neighborhoodPsiSite k R b r).hom) := by
  have := neighborhoodRetained_projection_smooth R V
  have : SmoothOfRelativeDimension 1 (neighborhoodPsiSourceMap R V r) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have : Smooth (neighborhoodPsiSourceMap R V r) :=
    SmoothOfRelativeDimension.smooth 1 _
  infer_instance

lemma neighborhoodCommon_total_smooth :
    Smooth (neighborhoodCommonSourceMap R V r ≫ (neighborhoodCommonSite k R b V r).hom) := by
  have := neighborhoodRetained_projection_smooth R V
  have : SmoothOfRelativeDimension 1 (neighborhoodCommonSourceMap R V r) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have : Smooth (neighborhoodCommonSourceMap R V r) :=
    SmoothOfRelativeDimension.smooth 1 _
  infer_instance

instance : IsOpenImmersion (commonNeighborhoodToSectionSource R V r) := by
  have : IsOpenImmersion (commonNeighborhoodToSectionSource R V r ≫
      (neighborhoodSourceOpen R V r).ι) := by
    rw [commonNeighborhoodToSectionSource_ι]
    infer_instance
  exact IsOpenImmersion.of_comp _ (neighborhoodSourceOpen R V r).ι
end AlgebraicGeometry.RelativeProjectiveLine
