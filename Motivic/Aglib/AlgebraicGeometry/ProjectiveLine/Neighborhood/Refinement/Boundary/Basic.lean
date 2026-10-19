module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.FixedOpen.Boundary.Map
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Graph.Boundary
/-! # The literal common source and whole relative boundary for lambda and psi -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R] (V : (Spec (.of (Polynomial R))).Opens) (r : R)

abbrev commonNeighborhoodSource := V ⊓ fixedPsiSource R r
abbrev commonNeighborhoodToV : (commonNeighborhoodSource R V r).toScheme ⟶ V.toScheme :=
  (Spec (.of (Polynomial R))).homOfLE inf_le_left
abbrev commonNeighborhoodToPsi : (commonNeighborhoodSource R V r).toScheme ⟶
    (fixedPsiSource R r).toScheme :=
  (Spec (.of (Polynomial R))).homOfLE inf_le_right

@[reassoc (attr := simp)] lemma commonNeighborhoodToV_ι :
    commonNeighborhoodToV R V r ≫ V.ι = (commonNeighborhoodSource R V r).ι :=
  Scheme.homOfLE_ι _ _
@[reassoc (attr := simp)] lemma commonNeighborhoodToPsi_ι :
    commonNeighborhoodToPsi R V r ≫ (fixedPsiSource R r).ι =
      (commonNeighborhoodSource R V r).ι := Scheme.homOfLE_ι _ _

abbrev commonNeighborhoodProjection :=
  (commonNeighborhoodSource R V r).ι ≫ Scheme.Hom.boundaryLineProjection R
abbrev commonNeighborhoodAmbient := pullback (commonNeighborhoodProjection R V r)
  (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))
abbrev commonNeighborhoodMissing := pullback (commonNeighborhoodProjection R V r)
  (neighborhoodBoundaryInclusion R V ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))
abbrev commonNeighborhoodZero := pullback (commonNeighborhoodProjection R V r)
  (Scheme.Hom.boundaryCoordinateMap R R (Polynomial.evalRingHom 0) ≫
    Scheme.Hom.boundaryLineProjection R)
abbrev commonNeighborhoodBoundary := commonNeighborhoodMissing R V r ⨿
  commonNeighborhoodZero R V r

lemma commonNeighborhoodProjection_graph : commonNeighborhoodProjection R V r =
    commonNeighborhoodToV R V r ≫ neighborhoodProjection R V := by
  rw [neighborhoodProjection, neighborhoodProjection_eq, ← Category.assoc, commonNeighborhoodToV_ι]
lemma commonNeighborhoodProjection_psi : commonNeighborhoodProjection R V r =
    commonNeighborhoodToPsi R V r ≫ fixedPsiProjection R r := by
  rw [fixedPsiProjection, ← Category.assoc, commonNeighborhoodToPsi_ι]

def commonNeighborhoodToGraphAmbient : commonNeighborhoodAmbient R V r ⟶
    neighborhoodGraphAmbient R V :=
  pullback.lift (pullback.fst _ _ ≫ commonNeighborhoodToV R V r) (pullback.snd _ _)
    (by rw [Category.assoc, ← commonNeighborhoodProjection_graph]; exact pullback.condition)
def commonNeighborhoodToPsiAmbient : commonNeighborhoodAmbient R V r ⟶
    fixedPsiAmbient R r :=
  pullback.lift (pullback.fst _ _ ≫ commonNeighborhoodToPsi R V r) (pullback.snd _ _)
    (by rw [Category.assoc, ← commonNeighborhoodProjection_psi]; exact pullback.condition)

def commonNeighborhoodMissingToGraph : commonNeighborhoodMissing R V r ⟶
    pullback (pullback.snd (neighborhoodProjection R V) (ProjectiveSpace.toSpec R _))
      (neighborhoodBoundaryInclusion R V) :=
  pullback.lift
    (pullback.lift (pullback.fst _ _ ≫ commonNeighborhoodToV R V r)
      (pullback.snd _ _ ≫ neighborhoodBoundaryInclusion R V) (by
        rw [Category.assoc, ← commonNeighborhoodProjection_graph, Category.assoc]
        exact pullback.condition))
    (pullback.snd _ _) (by simp)

def commonNeighborhoodMissingToPsi : commonNeighborhoodMissing R V r ⟶ fixedPsiMissing R V r :=
  pullback.lift (pullback.fst _ _ ≫ commonNeighborhoodToPsi R V r) (pullback.snd _ _)
    (by rw [Category.assoc, ← commonNeighborhoodProjection_psi]; exact pullback.condition)

def commonNeighborhoodZeroToPsi : commonNeighborhoodZero R V r ⟶ fixedPsiZero R r :=
  pullback.lift (pullback.fst _ _ ≫ commonNeighborhoodToPsi R V r) (pullback.snd _ _)
    (by rw [Category.assoc, ← commonNeighborhoodProjection_psi]; exact pullback.condition)

variable (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)

def commonNeighborhoodZeroToGraph : commonNeighborhoodZero R V r ⟶
    pullback (neighborhoodProjection R V) (neighborhoodZero R V hV ≫
      neighborhoodInclusion R V ≫ ProjectiveSpace.toSpec R _) :=
  pullback.lift (pullback.fst _ _ ≫ commonNeighborhoodToV R V r) (pullback.snd _ _) (by
    rw [Category.assoc, ← commonNeighborhoodProjection_graph, pullback.condition]
    congr 1
    rw [← Category.assoc, neighborhoodZero_inclusion]
    simp only [zeroSection, Category.assoc, chart_toSpec,
      Scheme.Hom.boundaryCoordinateMap, Scheme.Hom.boundaryLineProjection])

def commonNeighborhoodBoundaryToGraph : commonNeighborhoodBoundary R V r ⟶
    neighborhoodGraphBoundarySource R V hV :=
  coprod.map (commonNeighborhoodMissingToGraph R V r) (commonNeighborhoodZeroToGraph R V r hV)

def commonNeighborhoodBoundaryToPsi : commonNeighborhoodBoundary R V r ⟶ fixedPsiBoundary R V r :=
  coprod.map (commonNeighborhoodMissingToPsi R V r) (commonNeighborhoodZeroToPsi R V r)

end AlgebraicGeometry.RelativeProjectiveLine
