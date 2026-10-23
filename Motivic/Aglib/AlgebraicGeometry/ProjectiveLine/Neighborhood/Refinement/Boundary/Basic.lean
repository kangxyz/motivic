/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
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

/-- The intersection of the original neighborhood and the fixed psi source. -/
abbrev commonNeighborhoodSource := V ⊓ fixedPsiSource R r
/-- The inclusion of the common source into the original neighborhood. -/
abbrev commonNeighborhoodToV : (commonNeighborhoodSource R V r).toScheme ⟶ V.toScheme :=
  (Spec (.of (Polynomial R))).homOfLE inf_le_left
/-- The inclusion of the common source into the fixed psi source. -/
abbrev commonNeighborhoodToPsi : (commonNeighborhoodSource R V r).toScheme ⟶
    (fixedPsiSource R r).toScheme :=
  (Spec (.of (Polynomial R))).homOfLE inf_le_right

@[reassoc] lemma commonNeighborhoodToV_ι :
    commonNeighborhoodToV R V r ≫ V.ι = (commonNeighborhoodSource R V r).ι :=
  Scheme.homOfLE_ι _ _
@[reassoc] lemma commonNeighborhoodToPsi_ι :
    commonNeighborhoodToPsi R V r ≫ (fixedPsiSource R r).ι =
      (commonNeighborhoodSource R V r).ι := Scheme.homOfLE_ι _ _

/-- The structural morphism of the common source to the coefficient base. -/
abbrev commonNeighborhoodProjection :=
  (commonNeighborhoodSource R V r).ι ≫ Scheme.Hom.boundaryLineProjection R
/-- The projective-line product over the common source. -/
abbrev commonNeighborhoodAmbient := pullback (commonNeighborhoodProjection R V r)
  (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))
/-- The missing boundary pulled back to the common source. -/
abbrev commonNeighborhoodMissing := pullback (commonNeighborhoodProjection R V r)
  (neighborhoodBoundaryInclusion R V ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))
/-- The whole zero boundary pulled back to the common source. -/
abbrev commonNeighborhoodZero := pullback (commonNeighborhoodProjection R V r)
  (Scheme.Hom.boundaryCoordinateMap R R (Polynomial.evalRingHom 0) ≫
    Scheme.Hom.boundaryLineProjection R)
/-- The coproduct of the missing and zero boundaries over the common source. -/
abbrev commonNeighborhoodBoundary := commonNeighborhoodMissing R V r ⨿
  commonNeighborhoodZero R V r

lemma commonNeighborhoodProjection_graph : commonNeighborhoodProjection R V r =
    commonNeighborhoodToV R V r ≫ neighborhoodProjection R V := by
  rw [neighborhoodProjection, neighborhoodProjection_eq, ← Category.assoc, commonNeighborhoodToV_ι]
lemma commonNeighborhoodProjection_psi : commonNeighborhoodProjection R V r =
    commonNeighborhoodToPsi R V r ≫ fixedPsiProjection R r := by
  rw [fixedPsiProjection, ← Category.assoc, commonNeighborhoodToPsi_ι]

/-- The common ambient map to the original graph ambient scheme. -/
def commonNeighborhoodToGraphAmbient : commonNeighborhoodAmbient R V r ⟶
    neighborhoodGraphAmbient R V :=
  pullback.lift (pullback.fst _ _ ≫ commonNeighborhoodToV R V r) (pullback.snd _ _)
    (by rw [Category.assoc, ← commonNeighborhoodProjection_graph]; exact pullback.condition)
/-- The common ambient map to the fixed psi ambient scheme. -/
def commonNeighborhoodToPsiAmbient : commonNeighborhoodAmbient R V r ⟶
    fixedPsiAmbient R r :=
  pullback.lift (pullback.fst _ _ ≫ commonNeighborhoodToPsi R V r) (pullback.snd _ _)
    (by rw [Category.assoc, ← commonNeighborhoodProjection_psi]; exact pullback.condition)

/-- The missing-boundary map to the original graph boundary component. -/
def commonNeighborhoodMissingToGraph : commonNeighborhoodMissing R V r ⟶
    pullback (pullback.snd (neighborhoodProjection R V) (ProjectiveSpace.toSpec R _))
      (neighborhoodBoundaryInclusion R V) :=
  pullback.lift
    (pullback.lift (pullback.fst _ _ ≫ commonNeighborhoodToV R V r)
      (pullback.snd _ _ ≫ neighborhoodBoundaryInclusion R V) (by
        rw [Category.assoc, ← commonNeighborhoodProjection_graph, Category.assoc]
        exact pullback.condition))
    (pullback.snd _ _) (by simp)

/-- The missing-boundary map to the fixed psi boundary component. -/
def commonNeighborhoodMissingToPsi : commonNeighborhoodMissing R V r ⟶ fixedPsiMissing R V r :=
  pullback.lift (pullback.fst _ _ ≫ commonNeighborhoodToPsi R V r) (pullback.snd _ _)
    (by rw [Category.assoc, ← commonNeighborhoodProjection_psi]; exact pullback.condition)

/-- The whole-zero map to the fixed psi boundary component. -/
def commonNeighborhoodZeroToPsi : commonNeighborhoodZero R V r ⟶ fixedPsiZero R r :=
  pullback.lift (pullback.fst _ _ ≫ commonNeighborhoodToPsi R V r) (pullback.snd _ _)
    (by rw [Category.assoc, ← commonNeighborhoodProjection_psi]; exact pullback.condition)

variable (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)

/-- The whole-zero map to the original graph boundary component. -/
def commonNeighborhoodZeroToGraph : commonNeighborhoodZero R V r ⟶
    pullback (neighborhoodProjection R V) (neighborhoodZero R V hV ≫
      neighborhoodInclusion R V ≫ ProjectiveSpace.toSpec R _) :=
  pullback.lift (pullback.fst _ _ ≫ commonNeighborhoodToV R V r) (pullback.snd _ _) (by
    rw [Category.assoc, ← commonNeighborhoodProjection_graph, pullback.condition]
    congr 1
    rw [← Category.assoc, neighborhoodZero_inclusion]
    simp only [zeroSection, Category.assoc, chart_toSpec,
      Scheme.Hom.boundaryCoordinateMap, Scheme.Hom.boundaryLineProjection])

/-- The coproduct boundary map to the original graph boundary. -/
def commonNeighborhoodBoundaryToGraph : commonNeighborhoodBoundary R V r ⟶
    neighborhoodGraphBoundarySource R V hV :=
  coprod.map (commonNeighborhoodMissingToGraph R V r) (commonNeighborhoodZeroToGraph R V r hV)

/-- The coproduct boundary map to the fixed psi boundary. -/
def commonNeighborhoodBoundaryToPsi : commonNeighborhoodBoundary R V r ⟶ fixedPsiBoundary R V r :=
  coprod.map (commonNeighborhoodMissingToPsi R V r) (commonNeighborhoodZeroToPsi R V r)

end AlgebraicGeometry.RelativeProjectiveLine
