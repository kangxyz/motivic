module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Graph.Boundary
/-! # The actual whole graph boundary projects to the original finite boundary -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R]
variable (V : (Spec (.of (Polynomial R))).Opens)
variable (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)

/-- Project each component of the graph boundary to the corresponding original boundary component.
-/
def neighborhoodGraphBoundaryToOriginal : neighborhoodGraphBoundarySource R V hV ⟶
    neighborhoodBoundary R V ⨿ Spec (.of R) :=
  coprod.map (pullback.snd _ _) (pullback.snd _ _)

@[reassoc]
lemma neighborhoodGraphBoundaryToOriginal_fac :
    neighborhoodGraphBoundaryMap R V hV ≫ pullback.snd _ _ =
      neighborhoodGraphBoundaryToOriginal R V hV ≫ fullNeighborhoodBoundaryMap R V := by
  apply coprod.hom_ext
  · simp only [neighborhoodGraphBoundaryMap, Scheme.Hom.fullBoundaryProductMap,
      coprod.inl_desc_assoc, neighborhoodGraphBoundaryToOriginal, coprod.inl_map_assoc,
      fullNeighborhoodBoundaryMap, coprod.inl_desc]
    exact pullback.condition
  · simp [neighborhoodGraphBoundaryMap, Scheme.Hom.fullBoundaryProductMap,
      neighborhoodGraphBoundaryToOriginal, fullNeighborhoodBoundaryMap,
      Scheme.Hom.graphBoundaryRestriction, zeroSection]

/-- The graph boundary factors through the single original base-change boundary.
This is the map used to pull back its common positive-twist unit; no component
of the whole boundary is discarded. -/
def neighborhoodGraphBoundaryToProduct : neighborhoodGraphBoundarySource R V hV ⟶
    pullback (neighborhoodProjection R V)
      (fullNeighborhoodBoundaryMap R V ≫ ProjectiveSpace.toSpec R _) :=
  pullback.lift (neighborhoodGraphBoundaryMap R V hV ≫ pullback.fst _ _)
    (neighborhoodGraphBoundaryToOriginal R V hV) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc,
        neighborhoodGraphBoundaryToOriginal_fac, Category.assoc])

@[reassoc (attr := simp)]
lemma neighborhoodGraphBoundaryToProduct_snd :
    neighborhoodGraphBoundaryToProduct R V hV ≫ pullback.snd _ _ =
      neighborhoodGraphBoundaryToOriginal R V hV := pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
lemma neighborhoodGraphBoundaryToProduct_fst :
    neighborhoodGraphBoundaryToProduct R V hV ≫ pullback.fst _ _ =
      neighborhoodGraphBoundaryMap R V hV ≫ pullback.fst _ _ := pullback.lift_fst _ _ _
end AlgebraicGeometry.RelativeProjectiveLine
