/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Refinement.Retained.Graph
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Refinement.Pole
/-! # The original graph-times-pole coefficient on the actual retained curve -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
open Scheme.Modules.Invertible.PullbackTensor.Local
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R]
  (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme] (r : R)
  (l m : ℕ)

/-- The line bundle given by the ideal of the common neighborhood graph. -/
def commonNeighborhoodGraphLine : LineBundle (commonNeighborhoodAmbient R V r) :=
  ⟨Scheme.Hom.idealModule (commonNeighborhoodGraph R V r), commonNeighborhoodGraph_rankOne R V r⟩

/-- The line bundle given by the ideal of the retained common neighborhood graph. -/
def commonNeighborhoodRetainedGraphLine : LineBundle (commonNeighborhoodRetainedCurve R V r) :=
  ⟨Scheme.Hom.idealModule (commonNeighborhoodRetainedGraph R V r),
    isLocallyRankOne_of_iso _ (commonNeighborhoodRetainedGraphIdealIso R V r)
      (pullbackLineBundle (commonNeighborhoodRetainedInclusion R V r)
        (commonNeighborhoodGraphLine R V r)).property⟩

/-- The restriction of the common neighborhood pole line to the retained curve. -/
def commonNeighborhoodRetainedPoleLine : LineBundle (commonNeighborhoodRetainedCurve R V r) :=
  pullbackLineBundle (commonNeighborhoodRetainedInclusion R V r)
    (commonNeighborhoodPoleLine R V r l m)

/-- The tensor product of the retained graph ideal line and the retained pole line. -/
def commonNeighborhoodGraphDomainLine : LineBundle (commonNeighborhoodRetainedCurve R V r) :=
  tensorLineBundle _ (commonNeighborhoodRetainedGraphLine R V r)
    (commonNeighborhoodRetainedPoleLine R V r l m)

/-- The comparison from the retained graph domain line to the restricted pencil line. -/
def commonNeighborhoodRetainedPencilIso :
    (commonNeighborhoodGraphDomainLine R V r l m).val ≅
      (pullbackLineBundle (commonNeighborhoodRetainedInclusion R V r)
        (commonNeighborhoodPencilLine R V r l m)).val :=
  tensorSheafIso _ (commonNeighborhoodRetainedGraphIdealIso R V r).symm (Iso.refl _) ≪≫
    (pullbackLineBundleTensorIso (commonNeighborhoodRetainedInclusion R V r)
      (commonNeighborhoodGraphLine R V r) (commonNeighborhoodPoleLine R V r l m)).symm ≪≫
    (Scheme.Modules.pullback (commonNeighborhoodRetainedInclusion R V r)).mapIso
      (commonNeighborhoodGraphPencilIso R V r (neighborhoodLocalTwist R V r l)
        (fixedPsiTwistLine R r m))

variable (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)
  (e : neighborhoodFrame R V r l)
lemma NeighborhoodSectionPair.retainedPencilIso_start
    (d : NeighborhoodSectionPair R V hV r l e)
    (t : SheafOfModules.unit (fixedPsiAmbient R r).ringCatSheaf ⟶
      (fixedPsiTwistLine R r m).val) :
    (commonNeighborhoodRetainedPencilIso R V r l m).hom ≫
      Scheme.Modules.Hom.pullbackToUnit (d.pencilStart R V hV r l m e t)
        (commonNeighborhoodRetainedInclusion R V r) =
    Scheme.Modules.Hom.productSection
      (Scheme.Hom.idealInclusion (commonNeighborhoodRetainedGraph R V r))
      (Scheme.Modules.Hom.pullbackToUnit (d.poleFunctional R V hV r l m e t)
        (commonNeighborhoodRetainedInclusion R V r)) := by
  simp only [commonNeighborhoodRetainedPencilIso, Iso.trans_hom, Category.assoc,
    Functor.mapIso_hom]
  rw [show (Scheme.Modules.pullback (commonNeighborhoodRetainedInclusion R V r)).map
      (commonNeighborhoodGraphPencilIso R V r (neighborhoodLocalTwist R V r l)
        (fixedPsiTwistLine R r m)).hom ≫
      Scheme.Modules.Hom.pullbackToUnit (d.pencilStart R V hV r l m e t)
        (commonNeighborhoodRetainedInclusion R V r) =
      Scheme.Modules.Hom.pullbackToUnit
        ((commonNeighborhoodGraphPencilIso R V r (neighborhoodLocalTwist R V r l)
          (fixedPsiTwistLine R r m)).hom ≫ d.pencilStart R V hV r l m e t)
        (commonNeighborhoodRetainedInclusion R V r) by
    simp only [Scheme.Modules.Hom.pullbackToUnit, Functor.map_comp, Category.assoc]]
  dsimp only [NeighborhoodSectionPair.pencilStart, mixedProductFunctional]
  rw [commonNeighborhoodGraphPencilIso_start]
  rw [Scheme.Modules.Hom.pullbackToUnit_productSection_lineBundle
    (commonNeighborhoodRetainedInclusion R V r) (commonNeighborhoodGraphLine R V r)
    (commonNeighborhoodPoleLine R V r l m)]
  simp only [Iso.symm_hom, Iso.inv_hom_id_assoc]
  rw [tensorSheafIso_productSection]
  simp only [Iso.refl_hom, Category.id_comp]
  rw [← commonNeighborhoodRetainedGraphIdealIso_inclusion R V r]
  simp only [Iso.symm_hom, Iso.inv_hom_id_assoc]
  rfl
end AlgebraicGeometry.RelativeProjectiveLine
