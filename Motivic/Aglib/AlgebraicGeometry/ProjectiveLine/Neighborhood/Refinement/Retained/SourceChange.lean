module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Refinement.Pencil.Geometry
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Refinement.Cartesian
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.FixedOpen.RetainedGeometry
/-! # Cartesian changes of the actual retained lambda and psi curves -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R] (V : (Spec (.of (Polynomial R))).Opens) (r : R)

/-- The source-change map from the retained common curve to the retained neighborhood curve. -/
def commonNeighborhoodRetainedToGraph : commonNeighborhoodRetainedCurve R V r ⟶
    neighborhoodRetainedCurve R V :=
  Scheme.constantSourceMapOfEq (commonNeighborhoodToV R V r) (neighborhoodProjection R V)
    ((neighborhoodRetainedOpen R V).ι ≫ ProjectiveSpace.toSpec R _)
    (commonNeighborhoodProjection R V r) (commonNeighborhoodProjection_graph R V r)

/-- The source-change map from the retained common curve to the retained fixed Psi curve. -/
def commonNeighborhoodRetainedToPsi : commonNeighborhoodRetainedCurve R V r ⟶
    fixedPsiRetainedCurve R r V :=
  Scheme.constantSourceMapOfEq (commonNeighborhoodToPsi R V r) (fixedPsiProjection R r)
    ((neighborhoodRetainedOpen R V).ι ≫ ProjectiveSpace.toSpec R _)
    (commonNeighborhoodProjection R V r) (commonNeighborhoodProjection_psi R V r)

@[reassoc (attr := simp)] lemma commonNeighborhoodRetainedToGraph_fst :
    commonNeighborhoodRetainedToGraph R V r ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ commonNeighborhoodToV R V r :=
  Scheme.constantSourceMapOfEq_fst _ _ _ _ _
@[reassoc (attr := simp)] lemma commonNeighborhoodRetainedToGraph_snd :
    commonNeighborhoodRetainedToGraph R V r ≫ pullback.snd _ _ = pullback.snd _ _ :=
  Scheme.constantSourceMapOfEq_snd _ _ _ _ _
@[reassoc (attr := simp)] lemma commonNeighborhoodRetainedToPsi_fst :
    commonNeighborhoodRetainedToPsi R V r ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ commonNeighborhoodToPsi R V r :=
  Scheme.constantSourceMapOfEq_fst _ _ _ _ _
@[reassoc (attr := simp)] lemma commonNeighborhoodRetainedToPsi_snd :
    commonNeighborhoodRetainedToPsi R V r ≫ pullback.snd _ _ = pullback.snd _ _ :=
  Scheme.constantSourceMapOfEq_snd _ _ _ _ _

lemma commonNeighborhoodRetainedToGraph_isPullback :
    IsPullback (commonNeighborhoodRetainedToGraph R V r) (pullback.fst _ _)
      (pullback.fst _ _) (commonNeighborhoodToV R V r) :=
  Scheme.constantSourceMapOfEq_isPullback _ _ _ _ _
lemma commonNeighborhoodRetainedToPsi_isPullback :
    IsPullback (commonNeighborhoodRetainedToPsi R V r) (pullback.fst _ _)
      (pullback.fst _ _) (commonNeighborhoodToPsi R V r) :=
  Scheme.constantSourceMapOfEq_isPullback _ _ _ _ _

instance : IsOpenImmersion (commonNeighborhoodRetainedToGraph R V r) :=
  MorphismProperty.of_isPullback (commonNeighborhoodRetainedToGraph_isPullback R V r).flip
    inferInstance
instance : IsOpenImmersion (commonNeighborhoodRetainedToPsi R V r) :=
  MorphismProperty.of_isPullback (commonNeighborhoodRetainedToPsi_isPullback R V r).flip
    inferInstance

@[reassoc] lemma commonNeighborhoodRetainedToGraph_inclusion :
    commonNeighborhoodRetainedToGraph R V r ≫ neighborhoodRetainedInclusion R V =
      commonNeighborhoodRetainedInclusion R V r ≫ commonNeighborhoodToGraphAmbient R V r := by
  apply pullback.hom_ext <;>
    simp [commonNeighborhoodToGraphAmbient]

@[reassoc] lemma commonNeighborhoodRetainedToPsi_inclusion :
    commonNeighborhoodRetainedToPsi R V r ≫ fixedPsiRetainedInclusion R r V =
      commonNeighborhoodRetainedInclusion R V r ≫ commonNeighborhoodToPsiAmbient R V r := by
  apply pullback.hom_ext <;>
    simp [commonNeighborhoodToPsiAmbient, fixedPsiRetainedInclusion,
      fixedPsiProductBoundaryMap]

/-- The retained inclusion square is Cartesian, not merely commutative. -/
lemma commonNeighborhoodRetainedToGraph_inclusion_isPullback :
    IsPullback (commonNeighborhoodRetainedToGraph R V r)
      (commonNeighborhoodRetainedInclusion R V r) (neighborhoodRetainedInclusion R V)
      (commonNeighborhoodToGraphAmbient R V r) := by
  apply IsPullback.of_bot
    (v₂₁ := pullback.fst (commonNeighborhoodProjection R V r) (ProjectiveSpace.toSpec R _))
    (v₂₂ := pullback.fst (neighborhoodProjection R V) (ProjectiveSpace.toSpec R _))
  · simpa only [commonNeighborhoodRetainedInclusion_fst, neighborhoodRetainedInclusion_fst]
      using commonNeighborhoodRetainedToGraph_isPullback R V r
  · exact commonNeighborhoodRetainedToGraph_inclusion R V r
  · exact commonNeighborhoodToGraphAmbient_isPullback R V r

lemma commonNeighborhoodRetainedToPsi_inclusion_isPullback :
    IsPullback (commonNeighborhoodRetainedToPsi R V r)
      (commonNeighborhoodRetainedInclusion R V r) (fixedPsiRetainedInclusion R r V)
      (commonNeighborhoodToPsiAmbient R V r) := by
  apply IsPullback.of_bot
    (v₂₁ := pullback.fst (commonNeighborhoodProjection R V r) (ProjectiveSpace.toSpec R _))
    (v₂₂ := pullback.fst (fixedPsiProjection R r) (ProjectiveSpace.toSpec R _))
  · simpa only [commonNeighborhoodRetainedInclusion_fst, fixedPsiRetainedInclusion_fst]
      using commonNeighborhoodRetainedToPsi_isPullback R V r
  · exact commonNeighborhoodRetainedToPsi_inclusion R V r
  · exact commonNeighborhoodToPsiAmbient_isPullback R V r
end AlgebraicGeometry.RelativeProjectiveLine
