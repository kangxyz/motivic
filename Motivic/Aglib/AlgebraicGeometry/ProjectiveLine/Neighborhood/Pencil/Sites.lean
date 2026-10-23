/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Refinement.Retained.SectionChange
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Refinement.Retained.Graph
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Basic
/-! # Actual smooth-site sources and the original target of the relative neighborhood pencil -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
open _root_.AlgebraicGeometry.Scheme
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

/-- The common neighborhood source as an object of the smooth site over `Spec k`. -/
def neighborhoodCommonSite : SmoothSite (Spec (.of k)) := by
  have := commonNeighborhoodSource_affine R V r
  have : Smooth (commonNeighborhoodProjection R V r ≫ b) :=
    neighborhood_open_line_smooth k R b (commonNeighborhoodSource R V r).ι
  exact SmoothSite.mk (commonNeighborhoodProjection R V r ≫ b)

/-- The section source open as an object of the smooth site over `Spec k`. -/
def neighborhoodLambdaSite : SmoothSite (Spec (.of k)) := by
  have := neighborhoodSourceOpen_affine R V r
  have : Smooth (((neighborhoodSourceOpen R V r).ι ≫ neighborhoodProjection R V) ≫ b) := by
    simpa only [neighborhoodProjection, neighborhoodInclusion, Category.assoc,
      chart_toSpec, Scheme.Hom.boundaryLineProjection] using
      neighborhood_open_line_smooth k R b ((neighborhoodSourceOpen R V r).ι ≫ V.ι)
  exact SmoothSite.mk (((neighborhoodSourceOpen R V r).ι ≫ neighborhoodProjection R V) ≫ b)

/-- The fixed punctured source as an object of the smooth site over `Spec k`. -/
def neighborhoodPsiSite : SmoothSite (Spec (.of k)) := by
  have : Smooth (fixedPsiProjection R r ≫ b) :=
    neighborhood_open_line_smooth k R b (fixedPsiSource R r).ι
  exact SmoothSite.mk (fixedPsiProjection R r ≫ b)

/-- The retained projective open as an object of the smooth site over `Spec k`. -/
def neighborhoodTargetSite : SmoothSite (Spec (.of k)) := by
  have : IsAffine (neighborhoodRetainedOpen R V).toScheme := neighborhoodRetained_isAffineOpen R V
  have := neighborhoodRetained_projection_smooth R V
  have : Smooth ((neighborhoodRetainedOpen R V).ι ≫ ProjectiveSpace.toSpec R _) :=
    SmoothOfRelativeDimension.smooth 1 _
  exact SmoothSite.mk (((neighborhoodRetainedOpen R V).ι ≫ ProjectiveSpace.toSpec R _) ≫ b)

/-- The smooth-site map from the common source to the lambda section source. -/
def neighborhoodPencilAlpha : neighborhoodCommonSite k R b V r ⟶ neighborhoodLambdaSite k R b V r :=
  SmoothSite.homMk (commonNeighborhoodToSectionSource R V r) (by
    change commonNeighborhoodToSectionSource R V r ≫
      (((neighborhoodSourceOpen R V r).ι ≫ neighborhoodProjection R V) ≫ b) =
      commonNeighborhoodProjection R V r ≫ b
    simpa only [Category.assoc, commonNeighborhoodToSectionSource_ι_assoc] using
      congrArg (fun f => f ≫ b) (commonNeighborhoodProjection_graph R V r).symm)

/-- The smooth-site map from the common source to the fixed psi source. -/
def neighborhoodPencilBeta : neighborhoodCommonSite k R b V r ⟶ neighborhoodPsiSite k R b r :=
  SmoothSite.homMk (commonNeighborhoodToPsi R V r) (by
    simp only [neighborhoodCommonSite, neighborhoodPsiSite, SmoothSite.mk_hom, ← Category.assoc]
    exact congrArg (fun f => f ≫ b) (commonNeighborhoodProjection_psi R V r).symm)

/-- The smooth-site map from the common source to the retained target. -/
def neighborhoodPencilGraph : neighborhoodCommonSite k R b V r ⟶ neighborhoodTargetSite k R b V :=
  SmoothSite.homMk (commonNeighborhoodRetainedTargetMap R V r) (by
    simp only [neighborhoodCommonSite, neighborhoodTargetSite, SmoothSite.mk_hom,
      ← Category.assoc, commonNeighborhoodRetainedTargetMap_ι]
    simp only [commonNeighborhoodTargetMap, commonNeighborhoodProjection,
      Category.assoc, chart_toSpec, Scheme.Hom.boundaryLineProjection])
end AlgebraicGeometry.RelativeProjectiveLine
