module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Refinement.Pencil.Graph
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Refinement.Pencil.Geometry
/-! # The literal common graph inside the unchanged punctured target -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R]
  (V : (Spec (.of (Polynomial R))).Opens) (r : R)

/-- The common neighborhood graph with target restricted to the retained curve. -/
def commonNeighborhoodRetainedGraph : (commonNeighborhoodSource R V r).toScheme ⟶
    commonNeighborhoodRetainedCurve R V r :=
  pullback.lift (𝟙 _) (commonNeighborhoodRetainedTargetMap R V r) (by
    simp only [Category.id_comp, ← Category.assoc, commonNeighborhoodRetainedTargetMap_ι]
    simp only [commonNeighborhoodTargetMap, Category.assoc, chart_toSpec,
      Scheme.Hom.boundaryLineProjection])

@[reassoc (attr := simp)] lemma commonNeighborhoodRetainedGraph_fst :
    commonNeighborhoodRetainedGraph R V r ≫ pullback.fst _ _ = 𝟙 _ :=
  pullback.lift_fst _ _ _
@[reassoc (attr := simp)] lemma commonNeighborhoodRetainedGraph_snd :
    commonNeighborhoodRetainedGraph R V r ≫ pullback.snd _ _ =
      commonNeighborhoodRetainedTargetMap R V r := pullback.lift_snd _ _ _

lemma commonNeighborhoodRetainedGraph_inclusion :
    commonNeighborhoodRetainedGraph R V r ≫ commonNeighborhoodRetainedInclusion R V r =
      commonNeighborhoodGraph R V r := by
  apply pullback.hom_ext <;>
    simp only [Category.assoc, commonNeighborhoodRetainedInclusion_fst,
      commonNeighborhoodRetainedInclusion_snd, commonNeighborhoodRetainedGraph_fst,
      commonNeighborhoodRetainedGraph_snd_assoc, commonNeighborhoodGraph_fst,
      commonNeighborhoodGraph_snd, commonNeighborhoodRetainedTargetMap_ι]

lemma commonNeighborhoodRetainedGraph_isPullback :
    IsPullback (𝟙 _) (commonNeighborhoodRetainedGraph R V r)
      (commonNeighborhoodGraph R V r) (commonNeighborhoodRetainedInclusion R V r) :=
  IsPullback.of_horiz_isIso_mono ⟨by
    simpa only [Category.id_comp] using (commonNeighborhoodRetainedGraph_inclusion R V r).symm⟩

instance : IsClosedImmersion (commonNeighborhoodRetainedGraph R V r) :=
  MorphismProperty.of_isPullback (commonNeighborhoodRetainedGraph_isPullback R V r) inferInstance

variable [IsAffine V.toScheme]

/-- The pullback comparison from the common graph ideal to the retained graph ideal. -/
def commonNeighborhoodRetainedGraphIdealIso :
    (Scheme.Modules.pullback (commonNeighborhoodRetainedInclusion R V r)).obj
      (Scheme.Hom.idealModule (commonNeighborhoodGraph R V r)) ≅
        Scheme.Hom.idealModule (commonNeighborhoodRetainedGraph R V r) := by
  have := finiteLocallyFree_of_isLocallyRankOne _ (commonNeighborhoodGraph_rankOne R V r)
  have : (Scheme.Hom.idealModule (commonNeighborhoodGraph R V r)).IsQuasicoherent := inferInstance
  let H := commonNeighborhoodRetainedGraph_isPullback R V r
  let e := Scheme.Hom.idealPullbackMap _ _ _ _ H.w
  have : IsIso e := Scheme.Hom.idealPullbackMap_isIso_of_flat_ambient _ _ _ _ _ H
  exact asIso e

@[reassoc] lemma commonNeighborhoodRetainedGraphIdealIso_inclusion :
    (commonNeighborhoodRetainedGraphIdealIso R V r).hom ≫
      Scheme.Hom.idealInclusion (commonNeighborhoodRetainedGraph R V r) =
    Scheme.Modules.Hom.pullbackToUnit (Scheme.Hom.idealInclusion (commonNeighborhoodGraph R V r))
      (commonNeighborhoodRetainedInclusion R V r) :=
  Scheme.Hom.idealPullbackMap_inclusion _ _ _ _ _
end AlgebraicGeometry.RelativeProjectiveLine
