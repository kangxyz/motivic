module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.CommonNeighborhoodRetainedSectionChange
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.CommonNeighborhoodRetainedGraph
public import Motivic.AlgebraicGeometry.SmoothSite
/-! # Actual smooth-site sources and the original target of the relative neighborhood pencil -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (k R : Type u) [Field k] [CommRing R]
  (b : Spec (.of R) ⟶ Spec (.of k)) [Smooth b]
  (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme] (r : R)

lemma neighborhood_open_line_smooth {X : Scheme.{u}}
    (j : X ⟶ Spec (.of (Polynomial R))) [IsOpenImmersion j] :
    Smooth ((j ≫ Scheme.Hom.boundaryLineProjection R) ≫ b) := by
  have := Scheme.AffineLineEtaleCompactification.polynomialProjection_smooth_one R
  have : Smooth (Scheme.Hom.boundaryLineProjection R) :=
    SmoothOfRelativeDimension.smooth 1 _
  infer_instance

def neighborhoodCommonSite : SmoothSite (Spec (.of k)) := by
  have := commonNeighborhoodSource_affine R V r
  have : Smooth (commonNeighborhoodProjection R V r ≫ b) :=
    neighborhood_open_line_smooth k R b (commonNeighborhoodSource R V r).ι
  exact SmoothSite.mk (commonNeighborhoodProjection R V r ≫ b)

def neighborhoodLambdaSite : SmoothSite (Spec (.of k)) := by
  have := neighborhoodSourceOpen_affine R V r
  have : Smooth (((neighborhoodSourceOpen R V r).ι ≫ neighborhoodProjection R V) ≫ b) := by
    simpa only [neighborhoodProjection, neighborhoodInclusion, Category.assoc,
      chart_toSpec, Scheme.Hom.boundaryLineProjection] using
      neighborhood_open_line_smooth k R b ((neighborhoodSourceOpen R V r).ι ≫ V.ι)
  exact SmoothSite.mk (((neighborhoodSourceOpen R V r).ι ≫ neighborhoodProjection R V) ≫ b)

def neighborhoodPsiSite : SmoothSite (Spec (.of k)) := by
  have : Smooth (fixedPsiProjection R r ≫ b) :=
    neighborhood_open_line_smooth k R b (fixedPsiSource R r).ι
  exact SmoothSite.mk (fixedPsiProjection R r ≫ b)

def neighborhoodTargetSite : SmoothSite (Spec (.of k)) := by
  have : IsAffine (neighborhoodRetainedOpen R V).toScheme := neighborhoodRetained_isAffineOpen R V
  have := neighborhoodRetained_projection_smooth R V
  have : Smooth ((neighborhoodRetainedOpen R V).ι ≫ ProjectiveSpace.toSpec R _) :=
    SmoothOfRelativeDimension.smooth 1 _
  exact SmoothSite.mk (((neighborhoodRetainedOpen R V).ι ≫ ProjectiveSpace.toSpec R _) ≫ b)

def neighborhoodPencilAlpha : neighborhoodCommonSite k R b V r ⟶ neighborhoodLambdaSite k R b V r :=
  SmoothSite.homMk (commonNeighborhoodToSectionSource R V r) (by
    change commonNeighborhoodToSectionSource R V r ≫
      (((neighborhoodSourceOpen R V r).ι ≫ neighborhoodProjection R V) ≫ b) =
      commonNeighborhoodProjection R V r ≫ b
    simpa only [Category.assoc, commonNeighborhoodToSectionSource_ι_assoc] using
      congrArg (fun f => f ≫ b) (commonNeighborhoodProjection_graph R V r).symm)

def neighborhoodPencilBeta : neighborhoodCommonSite k R b V r ⟶ neighborhoodPsiSite k R b r :=
  SmoothSite.homMk (commonNeighborhoodToPsi R V r) (by
    simp only [neighborhoodCommonSite, neighborhoodPsiSite, SmoothSite.mk_hom, ← Category.assoc]
    exact congrArg (fun f => f ≫ b) (commonNeighborhoodProjection_psi R V r).symm)

def neighborhoodPencilGraph : neighborhoodCommonSite k R b V r ⟶ neighborhoodTargetSite k R b V :=
  SmoothSite.homMk (commonNeighborhoodRetainedTargetMap R V r) (by
    simp only [neighborhoodCommonSite, neighborhoodTargetSite, SmoothSite.mk_hom,
      ← Category.assoc, commonNeighborhoodRetainedTargetMap_ι]
    simp only [commonNeighborhoodTargetMap, commonNeighborhoodProjection,
      Category.assoc, chart_toSpec, Scheme.Hom.boundaryLineProjection])
end AlgebraicGeometry.RelativeProjectiveLine
