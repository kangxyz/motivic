module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Refinement.Graph
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Graph.LocalGraphFunctional
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Normalized.Retained.PencilComparison
/-! # The literal diagonal ideal under the actual common source change -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R] (V : (Spec (.of (Polynomial R))).Opens) (r : R)

instance : IsClosedImmersion (commonNeighborhoodGraph R V r) :=
  MorphismProperty.of_isPullback (commonNeighborhoodGraph_isPullback R V r) (by
    dsimp [Scheme.Hom.compactificationGraph]; infer_instance)

/-- The pullback comparison between the neighborhood graph line and the common graph ideal. -/
def commonNeighborhoodGraphIdealIso :
    (Scheme.Modules.pullback (commonNeighborhoodToGraphAmbient R V r)).obj
      (neighborhoodGraphLine R V).val ≅ Scheme.Hom.idealModule (commonNeighborhoodGraph R V r) := by
  let j := Scheme.Hom.compactificationGraph (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))
    (neighborhoodInclusion R V)
  have : IsClosedImmersion j := by
    dsimp [j, Scheme.Hom.compactificationGraph]; infer_instance
  have : (Scheme.Hom.idealModule j).IsQuasicoherent := by
    have := finiteLocallyFree_of_isLocallyRankOne (neighborhoodGraphLine R V).val
      (neighborhoodGraphLine R V).property
    exact inferInstanceAs ((neighborhoodGraphLine R V).val.IsQuasicoherent)
  let e := Scheme.Hom.idealPullbackMap j (commonNeighborhoodGraph R V r)
    (commonNeighborhoodToGraphAmbient R V r) (commonNeighborhoodToV R V r)
      (commonNeighborhoodGraph_isPullback R V r).w
  have : IsIso e := Scheme.Hom.idealPullbackMap_isIso_of_flat_ambient _ _ _ _ _
    (commonNeighborhoodGraph_isPullback R V r)
  exact asIso e

@[reassoc] lemma commonNeighborhoodGraphIdealIso_inclusion :
    (commonNeighborhoodGraphIdealIso R V r).hom ≫
      Scheme.Hom.idealInclusion (commonNeighborhoodGraph R V r) =
    Scheme.Modules.Hom.pullbackToUnit
      (Scheme.Hom.idealInclusion (Scheme.Hom.compactificationGraph
        (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) (neighborhoodInclusion R V)))
      (commonNeighborhoodToGraphAmbient R V r) :=
  Scheme.Hom.idealPullbackMap_inclusion _ _ _ _ _

variable [IsAffine V.toScheme]
/-- Original local lambda ideal, compared to the actual whole common graph ideal. -/
def commonNeighborhoodLocalGraphIdealIso :
    (Scheme.Modules.pullback (commonNeighborhoodToSectionAmbient R V r)).obj
      (neighborhoodLocalIdeal R V r).val ≅ Scheme.Hom.idealModule (commonNeighborhoodGraph R V r) :=
  (Scheme.Modules.pullback (commonNeighborhoodToSectionAmbient R V r)).mapIso
    ((restrictFunctorIsoPullback (neighborhoodSectionOpen R V r).ι).app
      (neighborhoodGraphLine R V).val) ≪≫
    ((Scheme.Modules.pullbackComp (commonNeighborhoodToSectionAmbient R V r)
      (neighborhoodSectionOpen R V r).ι ≪≫
      Scheme.Modules.pullbackCongr (commonNeighborhoodToSectionAmbient_ι R V r)).app
        (neighborhoodGraphLine R V).val) ≪≫ commonNeighborhoodGraphIdealIso R V r

@[reassoc] lemma commonNeighborhoodLocalGraphIdealIso_inclusion :
    (commonNeighborhoodLocalGraphIdealIso R V r).hom ≫
      Scheme.Hom.idealInclusion (commonNeighborhoodGraph R V r) =
    Scheme.Modules.Hom.pullbackToUnit (neighborhoodLocalGraphFunctional R V r)
      (commonNeighborhoodToSectionAmbient R V r) := by
  simp only [commonNeighborhoodLocalGraphIdealIso, Iso.trans_hom, Category.assoc,
    commonNeighborhoodGraphIdealIso_inclusion]
  change _ ≫ ((Scheme.Modules.pullbackComp (commonNeighborhoodToSectionAmbient R V r)
    (neighborhoodSectionOpen R V r).ι ≪≫
      Scheme.Modules.pullbackCongr (commonNeighborhoodToSectionAmbient_ι R V r)).hom.app
        (neighborhoodGraphLine R V).val) ≫ _ = _
  rw [← pullbackToUnit_comp_congr]
  simp only [Functor.mapIso_hom, Scheme.Modules.Hom.pullbackToUnit]
  rw [← Functor.map_comp_assoc]
  exact congrArg (fun a => (Scheme.Modules.pullback
    (commonNeighborhoodToSectionAmbient R V r)).map a ≫
      (pullbackUnitIso (commonNeighborhoodToSectionAmbient R V r)).hom)
    (neighborhoodLocalGraphFunctional_pullback R V r)
end AlgebraicGeometry.RelativeProjectiveLine
