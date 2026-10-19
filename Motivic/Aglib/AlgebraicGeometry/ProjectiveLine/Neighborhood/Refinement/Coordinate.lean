module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Refinement.Boundary.Basic
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Boundary.Coordinate
/-! # Literal lambda and psi coordinate equality on the whole common relative boundary -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R] (V : (Spec (.of (Polynomial R))).Opens) (r : R)

lemma fixedPsiBoundaryUnit_pullback_missing :
    Scheme.Hom.unitEndomorphismPullback coprod.inl (fixedPsiBoundaryUnit R V r).hom = 𝟙 _ := by
  apply Scheme.Hom.unitEndomorphismPullback_eq_of_restrict
  rw [fixedPsiBoundaryUnit_missing]
  simp only [Category.id_comp, Category.comp_id]

lemma fixedPsiBoundaryUnit_pullback_zero :
    Scheme.Hom.unitEndomorphismPullback coprod.inr (fixedPsiBoundaryUnit R V r).hom =
      Scheme.Hom.boundaryCoordinateEndomorphism R R (Polynomial.evalRingHom 0)
        (Scheme.Hom.boundaryProductMap (Scheme.Hom.boundaryLineProjection R)
          (fixedPsiSource R r).ι
          (Scheme.Hom.boundaryCoordinateMap R R (Polynomial.evalRingHom 0))) :=
  Scheme.Hom.unitEndomorphismPullback_eq_of_restrict _ _ _ (fixedPsiBoundaryUnit_zero R V r)

variable (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)

lemma commonNeighborhoodZero_coordinateMap_eq :
    commonNeighborhoodZeroToGraph R V r hV ≫ neighborhoodBoundaryCoordinateMap R V hV =
      commonNeighborhoodZeroToPsi R V r ≫
        Scheme.Hom.boundaryProductMap (Scheme.Hom.boundaryLineProjection R)
          (fixedPsiSource R r).ι
          (Scheme.Hom.boundaryCoordinateMap R R (Polynomial.evalRingHom 0)) := by
  apply pullback.hom_ext <;>
    simp [commonNeighborhoodZeroToGraph, neighborhoodBoundaryCoordinateMap,
      commonNeighborhoodZeroToPsi, Scheme.Hom.boundaryProductMap,
      pullback.congrHom_hom, pullback.map, Category.assoc]

/-- Exact equality on both original components, including their full scheme structures. -/
theorem commonNeighborhoodBoundary_coordinate_eq :
    Scheme.Hom.unitEndomorphismPullback (commonNeighborhoodBoundaryToGraph R V r hV)
      (neighborhoodBoundaryCoordinate R V hV) =
    Scheme.Hom.unitEndomorphismPullback (commonNeighborhoodBoundaryToPsi R V r)
      (fixedPsiBoundaryUnit R V r).hom := by
  apply Scheme.Hom.unitEndomorphism_ext_coprod
  · simp only [Scheme.Hom.unitEndomorphismPullback_comp, commonNeighborhoodBoundaryToGraph,
      commonNeighborhoodBoundaryToPsi, coprod.inl_map]
    rw [← Scheme.Hom.unitEndomorphismPullback_comp, ← Scheme.Hom.unitEndomorphismPullback_comp,
      neighborhoodBoundaryCoordinate_missing, fixedPsiBoundaryUnit_pullback_missing]
    simp [Scheme.Hom.unitEndomorphismPullback]
  · simp only [Scheme.Hom.unitEndomorphismPullback_comp, commonNeighborhoodBoundaryToGraph,
      commonNeighborhoodBoundaryToPsi, coprod.inr_map]
    rw [← Scheme.Hom.unitEndomorphismPullback_comp, ← Scheme.Hom.unitEndomorphismPullback_comp,
      neighborhoodBoundaryCoordinate_zero, fixedPsiBoundaryUnit_pullback_zero,
      ← Scheme.Hom.boundaryCoordinateEndomorphism_comp,
      ← Scheme.Hom.boundaryCoordinateEndomorphism_comp,
      commonNeighborhoodZero_coordinateMap_eq]
end AlgebraicGeometry.RelativeProjectiveLine
