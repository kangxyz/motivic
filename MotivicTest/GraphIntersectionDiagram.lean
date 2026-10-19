/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Graph.IntersectionDiagram
public import Mathlib.Data.ZMod.Basic

/-!
# Actual graph-incidence diagram consumers

These identify the actual support product and incidence embedding for right
identity and right graph generators. No flatness of the first support target
map is assumed. A separate nonreduced-base consumer checks the general graph
pair identity without importing any integral or reduced-scheme premise.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.MotivicTest.GraphIntersectionDiagram
open _root_.AlgebraicGeometry.Scheme.Products

variable {S X Y Z : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S}
  (A : FiniteCorrespondenceGenerator f g)

/-- Right identity support really yields the graph ambient product. -/
def rightIdentitySupportIso [IsIntegral Y] [IsSeparated g] :
    A.supportProduct (identityGenerator g) ≅ pullback (A.targetProjection ≫ g) g :=
  A.supportProductGraphIso (identityGenerator g)

/-- The literal identity-incidence embedding is the graph under the actual two isomorphisms. -/
theorem rightIdentityEmbedding [IsIntegral Y] [IsSeparated g] :
    A.incidenceToSupportProduct (identityGenerator g) ≫ (rightIdentitySupportIso A).hom =
      (A.rightIdentityIncidenceIso).hom ≫ _root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph
        A.targetProjection g :=
  A.incidenceToSupportProduct_graph (identityGenerator g)

/-- The same support-product comparison works for any actual graph on the right. -/
def rightGraphSupportIso (ψ : Y ⟶ Z) (w : ψ ≫ h = g)
    [IsIntegral Y] [IsSeparated h] :
    A.supportProduct (graphGeneratorOver ψ w) ≅ pullback (A.targetProjection ≫ g) g :=
  A.supportProductGraphIso (graphGeneratorOver ψ w)

/-- The four-factor middle map on right graph support is the literal graph pair map. -/
theorem rightGraphMiddlePair (ψ : Y ⟶ Z) (w : ψ ≫ h = g)
    [IsIntegral Y] [IsSeparated h] :
    A.supportProductInclusion (graphGeneratorOver ψ w) ≫ correspondenceMiddlePair f g h =
      (rightGraphSupportIso A ψ w).hom ≫ graphMiddlePair A.targetProjection g :=
  A.supportProductInclusion_middlePair (graphGeneratorOver ψ w)

/-- The generic graph square does not require a reduced base. -/
theorem nonreducedGraphDiagram :
    let S := Spec (CommRingCat.of (ZMod 4))
    _root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph (𝟙 S) (𝟙 S) ≫ graphMiddlePair (𝟙 S)
      (𝟙 S) =
      (𝟙 S) ≫ pullback.diagonal (𝟙 S) := by
  intro S
  exact _root_.AlgebraicGeometry.Scheme.Products.correspondenceGraph_middlePair (𝟙 S) (𝟙 S)

end Motivic.MotivicTest.GraphIntersectionDiagram
