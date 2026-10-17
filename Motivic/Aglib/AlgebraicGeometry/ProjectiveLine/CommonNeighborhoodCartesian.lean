module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.CommonNeighborhoodSectionMaps
/-! # Whole Cartesian source changes for the relative pencil -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R]
variable (V : (Spec (.of (Polynomial R))).Opens) (r : R)

lemma commonNeighborhoodToGraphAmbient_isPullback :
    IsPullback (commonNeighborhoodToGraphAmbient R V r)
      (pullback.fst (commonNeighborhoodProjection R V r) (ProjectiveSpace.toSpec R _))
      (pullback.fst (neighborhoodProjection R V) (ProjectiveSpace.toSpec R _))
      (commonNeighborhoodToV R V r) := by
  have he : commonNeighborhoodToGraphAmbient R V r =
      Scheme.constantSourceMapOfEq (commonNeighborhoodToV R V r) (neighborhoodProjection R V)
        (ProjectiveSpace.toSpec R _) (commonNeighborhoodProjection R V r)
          (commonNeighborhoodProjection_graph R V r) := by
    apply pullback.hom_ext <;> simp [commonNeighborhoodToGraphAmbient]
  rw [he]
  exact Scheme.constantSourceMapOfEq_isPullback _ _ _ _ _

lemma commonNeighborhoodToPsiAmbient_isPullback :
    IsPullback (commonNeighborhoodToPsiAmbient R V r)
      (pullback.fst (commonNeighborhoodProjection R V r) (ProjectiveSpace.toSpec R _))
      (pullback.fst (fixedPsiProjection R r) (ProjectiveSpace.toSpec R _))
      (commonNeighborhoodToPsi R V r) := by
  have he : commonNeighborhoodToPsiAmbient R V r =
      Scheme.constantSourceMapOfEq (commonNeighborhoodToPsi R V r) (fixedPsiProjection R r)
        (ProjectiveSpace.toSpec R _) (commonNeighborhoodProjection R V r)
          (commonNeighborhoodProjection_psi R V r) := by
    apply pullback.hom_ext <;> simp [commonNeighborhoodToPsiAmbient]
  rw [he]
  exact Scheme.constantSourceMapOfEq_isPullback _ _ _ _ _

instance : IsOpenImmersion (commonNeighborhoodToGraphAmbient R V r) :=
  MorphismProperty.of_isPullback (commonNeighborhoodToGraphAmbient_isPullback R V r).flip
    inferInstance
instance : IsOpenImmersion (commonNeighborhoodToPsiAmbient R V r) :=
  MorphismProperty.of_isPullback (commonNeighborhoodToPsiAmbient_isPullback R V r).flip
    inferInstance

instance [IsAffine V.toScheme] : IsOpenImmersion (commonNeighborhoodToSectionAmbient R V r) := by
  have : IsOpenImmersion (commonNeighborhoodToSectionAmbient R V r ≫
      ((neighborhoodProjectiveIso R V).hom ⁻¹ᵁ neighborhoodSerreOpen R V r).ι) := by
    rw [commonNeighborhoodToSectionAmbient_ι]
    infer_instance
  exact IsOpenImmersion.of_comp _
    ((neighborhoodProjectiveIso R V).hom ⁻¹ᵁ neighborhoodSerreOpen R V r).ι
end AlgebraicGeometry.RelativeProjectiveLine
