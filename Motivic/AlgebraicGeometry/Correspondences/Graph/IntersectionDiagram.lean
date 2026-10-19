/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Graph.PairGeometry

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Intersection.AmbientIdeal
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Support.Graphs

/-!
# The actual graph diagram for incidence with an isomorphic source projection

If the second correspondence support projects isomorphically to the middle
scheme, its product with the first support is the actual product of that
first support with the middle scheme. The incidence embedding becomes the
literal graph of the first support's target map. The four-factor middle map
becomes the corresponding pair map on this product. This applies to graph
and identity generators and supplies a geometric adapter for transversality;
no flatness of the first support's target map or Tor vanishing is asserted.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic
open _root_.AlgebraicGeometry.Scheme.Products

variable {S U Y : Scheme.{u}} (φ : U ⟶ Y) (g : Y ⟶ S)

namespace FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme.Products

variable {S X Y Z : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S}
  (A : FiniteCorrespondenceGenerator f g) (B : FiniteCorrespondenceGenerator g h)

/-- The actual support-product map induced by the second source projection. -/
noncomputable def supportProductToGraphProduct :
    A.supportProduct B ⟶ pullback (A.targetProjection ≫ g) g :=
  pullback.map (A.targetProjection ≫ g) (B.projection ≫ g)
    (A.targetProjection ≫ g) g (𝟙 A.scheme) B.projection (𝟙 S) (by simp) (by simp)

instance [IsIso B.projection] : IsIso (A.supportProductToGraphProduct B) := by
  unfold supportProductToGraphProduct
  infer_instance

@[reassoc (attr := simp)]
theorem supportProductToGraphProduct_fst :
    A.supportProductToGraphProduct B ≫ pullback.fst (A.targetProjection ≫ g) g =
      pullback.fst (A.targetProjection ≫ g) (B.projection ≫ g) := by
  simp only [supportProductToGraphProduct, pullback.map, pullback.lift_fst, Category.comp_id]

@[reassoc (attr := simp)]
theorem supportProductToGraphProduct_snd :
    A.supportProductToGraphProduct B ≫ pullback.snd (A.targetProjection ≫ g) g =
      pullback.snd (A.targetProjection ≫ g) (B.projection ≫ g) ≫ B.projection :=
  pullback.lift_snd _ _ _

/-- The support product is the actual graph ambient product when the source projection is an iso. -/
noncomputable def supportProductGraphIso [IsIso B.projection] :
    A.supportProduct B ≅ pullback (A.targetProjection ≫ g) g :=
  asIso (A.supportProductToGraphProduct B)

/-- The actual incidence embedding becomes the actual graph of the first target map. -/
@[reassoc]
theorem incidenceToSupportProduct_graph :
    A.incidenceToSupportProduct B ≫ A.supportProductToGraphProduct B =
      A.incidenceFst B ≫ _root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph
        A.targetProjection g := by
  apply pullback.hom_ext
  · simp
  · simp only [Category.assoc, supportProductToGraphProduct_snd,
      incidenceToSupportProduct_snd_assoc,
        _root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph_snd]
    exact (A.incidence_condition B).symm

/-- The four-factor middle map is literally the graph pair map on the support product. -/
@[reassoc]
theorem supportProductInclusion_middlePair :
    A.supportProductInclusion B ≫ correspondenceMiddlePair f g h =
      A.supportProductToGraphProduct B ≫ graphMiddlePair A.targetProjection g := by
  apply pullback.hom_ext
  · simp only [Category.assoc, correspondenceMiddlePair_fst,
      supportProductInclusion_fst_assoc, graphMiddlePair_fst,
      supportProductToGraphProduct_fst_assoc]
  · simp only [Category.assoc, correspondenceMiddlePair_snd,
      supportProductInclusion_snd_assoc, graphMiddlePair_snd,
      supportProductToGraphProduct_snd]
    rfl

end FiniteCorrespondenceGenerator

end Motivic
