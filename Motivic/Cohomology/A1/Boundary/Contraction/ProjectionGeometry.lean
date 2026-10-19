/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Products.ProductPermutation
public import Motivic.Cohomology.A1.Boundary.Contraction.Geometry
public import Motivic.Cohomology.A1.Contraction.RelativeNaturality

/-! # Literal parameter permutation for the projected zero-section boundary -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable (R : CommRingCat.{u}) (X : SmoothSite (Spec R))

/-- The Laurent open of the homotopy cylinder is the product Laurent open after
the displayed, actual permutation of the homotopy and boundary parameters. -/
theorem contractionOpen_productSwapLast :
    contractionOpen R (a1Cylinder R X) ≫ productSwapLast X (affineLine R) (affineLine R) =
      productSwapLast X (affineLine R) (torus R) ≫ a1Map R (contractionOpen R X) := by
  simpa only [contractionOpen, a1Map, a1Cylinder, torusCylinder, productMap_id] using
    productSwapLast_naturality X (affineLine R) (torus R)
      (𝟙 X) (𝟙 (affineLine R)) (torusInAffineLine R)

/-- The punctured projection is exactly the first projection after permutation. -/
theorem torusProjection_productSwapLast :
    productSwapLast X (affineLine R) (torus R) ≫ a1Projection R (torusCylinder R X) =
      productMap (a1Projection R X) (𝟙 (torus R)) :=
  productSwapLast_fst X (affineLine R) (torus R)

/-- The ambient projection is exactly the first projection after permutation. -/
theorem a1Projection_productSwapLast :
    productSwapLast X (affineLine R) (affineLine R) ≫ a1Projection R (a1Cylinder R X) =
      a1Map R (a1Projection R X) :=
  productSwapLast_fst X (affineLine R) (affineLine R)

/-- The zero section is the product zero section under the same literal permutation. -/
theorem a1Section_productSwapLast (a : R) :
    a1Section R (a1Cylinder R X) a ≫
        productSwapLast X (affineLine R) (affineLine R) =
      a1Map R (a1Section R X a) := by
  have hbase : productFst X (affineLine R) ≫
      (homMk X.hom (Category.comp_id _) : X ⟶ base (Spec R)) =
        homMk (a1Cylinder R X).hom (Category.comp_id _) := by
    apply MorphismProperty.Over.Hom.ext
    rfl
  apply product_hom_ext
  · apply product_hom_ext
    · simp [a1Section, a1Map, a1Cylinder, productSwapLast, Category.assoc]
    · simpa [a1Section, a1Map, a1Cylinder, productSwapLast, Category.assoc] using
        congrArg (fun f ↦ f ≫ affineLinePoint R a) hbase.symm
  · simp [a1Section, a1Map, a1Cylinder, productSwapLast, Category.assoc]

end AlgebraicGeometry.Scheme.SmoothSite

namespace Motivic.FiniteEtaleSite
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

open CategoryTheory.Limits

variable {k : Type u} [Field k] (X : SmoothSite (Spec (CommRingCat.of k)))

local notation "X₁" => SmoothSite.a1Cylinder (CommRingCat.of k) X
local notation "π" => SmoothSite.a1Projection (CommRingCat.of k) X
local notation "p" => SmoothSite.a1Map (CommRingCat.of k) π
local notation "q" => SmoothSite.productMap π (𝟙 (SmoothSite.torus (CommRingCat.of k)))
local notation "j₀" => SmoothSite.contractionOpen (CommRingCat.of k) X
local notation "j₁" => SmoothSite.contractionOpen (CommRingCat.of k) X₁
local notation "i₀" => SmoothSite.a1Section (CommRingCat.of k) X 0
local notation "i₁" => SmoothSite.a1Section (CommRingCat.of k) X₁ 0

/-- The iterated actual pullbacks in the zero-section projection square agree.
This is an isomorphism of neighborhood functors, not of coefficient inverse images. -/
def contractionZeroProjectionBaseChangeIso :
    baseChange (i₀).left ⋙ baseChange (π).left ≅ baseChange (p).left ⋙ baseChange (i₁).left :=
  (MorphismProperty.Over.pullbackComp (P := etaleSeparatedFiniteType) (Q := ⊤)
    (π).left (i₀).left (fg := (i₁ ≫ p).left)
      (hfg := congrArg (fun f ↦ f.left)
        (SmoothSite.a1Section_naturality (CommRingCat.of k) π 0))).symm ≪≫
    MorphismProperty.Over.pullbackComp (i₁).left (p).left

/-- The iterated actual pullbacks in the punctured projection square agree. -/
def contractionPunctureProjectionBaseChangeIso :
    baseChange (p).left ⋙ baseChange (j₁).left ≅ baseChange (j₀).left ⋙ baseChange (q).left :=
  (MorphismProperty.Over.pullbackComp (P := etaleSeparatedFiniteType) (Q := ⊤)
    (j₁).left (p).left).symm ≪≫
    MorphismProperty.Over.pullbackComp (q).left (j₀).left (fg := (j₁ ≫ p).left)
      (hfg := congrArg (fun f ↦ f.left)
        (SmoothSite.contractionOpen_naturality (CommRingCat.of k) π))

/-- The zero comparison retains the original ambient-neighborhood projection. -/
@[reassoc (attr := simp)]
theorem contractionZeroProjectionBaseChangeIso_fst
    (E : EtaleSeparatedFiniteType (X₁).left) :
    ((contractionZeroProjectionBaseChangeIso X).hom.app E).left ≫
        pullback.fst (pullback.snd E.hom (p).left) (i₁).left ≫ pullback.fst E.hom (p).left =
      pullback.fst (pullback.snd E.hom (i₀).left) (π).left ≫ pullback.fst E.hom (i₀).left := by
  simp [contractionZeroProjectionBaseChangeIso,
    MorphismProperty.Over.pullbackComp_hom_app_left,
    MorphismProperty.Over.pullbackComp_inv_app_left]

/-- The punctured comparison retains the original ambient-neighborhood projection. -/
@[reassoc (attr := simp)]
theorem contractionPunctureProjectionBaseChangeIso_fst
    (E : EtaleSeparatedFiniteType (X₁).left) :
    ((contractionPunctureProjectionBaseChangeIso X).hom.app E).left ≫
        pullback.fst (pullback.snd E.hom (j₀).left) (q).left ≫ pullback.fst E.hom (j₀).left =
      pullback.fst (pullback.snd E.hom (p).left) (j₁).left ≫ pullback.fst E.hom (p).left := by
  simp [contractionPunctureProjectionBaseChangeIso,
    MorphismProperty.Over.pullbackComp_hom_app_left,
    MorphismProperty.Over.pullbackComp_inv_app_left]

/-- The original base-changed test projects over the original test morphism. -/
theorem projectionRestriction_toBase (V : EtaleSeparatedFiniteType X.left) :
    (restrictionProjection (SmoothSite.a1Projection (CommRingCat.of k) X)).app V ≫ toBase X V =
      toBase (SmoothSite.a1Cylinder (CommRingCat.of k) X)
          ((baseChange (SmoothSite.a1Projection (CommRingCat.of k) X).left).obj V) ≫
        SmoothSite.a1Projection (CommRingCat.of k) X := by
  apply MorphismProperty.Over.Hom.ext
  exact pullback.condition

/-- A target cylinder neighborhood maps into the actual ambient pullback of the
source cylinder. The construction uses the original projection and needs no
replacement of an inverse-image coefficient sheaf. -/
def cylinderProjectionLift (V : EtaleSeparatedFiniteType X.left) :
    (cylinderNeighborhood (SmoothSite.a1Cylinder (CommRingCat.of k) X)).obj
        ((baseChange (SmoothSite.a1Projection (CommRingCat.of k) X).left).obj V) ⟶
      (baseChange (p).left).obj ((cylinderNeighborhood X).obj V) :=
  MorphismProperty.Over.homMk
    (pullback.lift
      (SmoothSite.a1Map (CommRingCat.of k)
        ((restrictionProjection (SmoothSite.a1Projection (CommRingCat.of k) X)).app V)).left
      ((cylinderNeighborhood (SmoothSite.a1Cylinder (CommRingCat.of k) X)).obj
        ((baseChange (SmoothSite.a1Projection (CommRingCat.of k) X).left).obj V)).hom (by
          change (SmoothSite.a1Map (CommRingCat.of k)
              ((restrictionProjection (SmoothSite.a1Projection (CommRingCat.of k) X)).app V) ≫
            SmoothSite.a1Map (CommRingCat.of k) (toBase X V)).left =
              (SmoothSite.a1Map (CommRingCat.of k)
                (toBase (SmoothSite.a1Cylinder (CommRingCat.of k) X)
                  ((baseChange (SmoothSite.a1Projection (CommRingCat.of k) X).left).obj V)) ≫
                SmoothSite.a1Map (CommRingCat.of k) π).left
          rw [← SmoothSite.a1Map_comp, ← SmoothSite.a1Map_comp, projectionRestriction_toBase]))
    (pullback.lift_snd _ _ _)

/-- The displayed lift keeps the literal original ambient-cylinder projection. -/
@[reassoc (attr := simp)]
theorem cylinderProjectionLift_fst (V : EtaleSeparatedFiniteType X.left) :
    (cylinderProjectionLift X V).left ≫
        pullback.fst ((cylinderNeighborhood X).obj V).hom
          (p).left =
      (SmoothSite.a1Map (CommRingCat.of k)
        ((restrictionProjection (SmoothSite.a1Projection (CommRingCat.of k) X)).app V)).left :=
  pullback.lift_fst _ _ _

/-- The original Laurent representative pulls back through the actual ambient
square by the literal product of the base projection with the identity on `Gₘ`. -/
theorem puncturedProjection_projection (V : EtaleSeparatedFiniteType X.left) :
    (toSmoothSite (SmoothSite.torusCylinder (CommRingCat.of k) X₁)).map
        ((baseChange (j₁).left).map (cylinderProjectionLift X V)) ≫
      (toSmoothSite (SmoothSite.torusCylinder (CommRingCat.of k) X₁)).map
        ((contractionPunctureProjectionBaseChangeIso X).hom.app
          ((cylinderNeighborhood X).obj V)) ≫
      (restrictionProjection q).app ((puncturedNeighborhood X).obj V) ≫
      puncturedProjection X V =
    puncturedProjection X₁ ((baseChange (π).left).obj V) ≫
      SmoothSite.productMap ((restrictionProjection π).app V)
        (𝟙 (SmoothSite.torus (CommRingCat.of k))) := by
  apply (cancel_mono
    (SmoothSite.contractionOpen (CommRingCat.of k) ((toSmoothSite X).obj V))).mp
  simp only [Category.assoc]
  rw [puncturedProjection_open,
    ← SmoothSite.contractionOpen_naturality (CommRingCat.of k)
      ((restrictionProjection π).app V),
    ← Category.assoc (puncturedProjection X₁ ((baseChange (π).left).obj V))]
  erw [puncturedProjection_open X₁ ((baseChange (π).left).obj V)]
  apply MorphismProperty.Over.Hom.ext
  change ((baseChange (j₁).left).map (cylinderProjectionLift X V)).left ≫
      ((contractionPunctureProjectionBaseChangeIso X).hom.app
        ((cylinderNeighborhood X).obj V)).left ≫
        pullback.fst (pullback.snd ((cylinderNeighborhood X).obj V).hom (j₀).left) (q).left ≫
        pullback.fst ((cylinderNeighborhood X).obj V).hom (j₀).left ≫ 𝟙 _ =
    pullback.fst ((cylinderNeighborhood X₁).obj ((baseChange (π).left).obj V)).hom (j₁).left ≫
      𝟙 _ ≫ (SmoothSite.a1Map (CommRingCat.of k) ((restrictionProjection π).app V)).left
  simp only [Category.comp_id, Category.id_comp]
  rw [contractionPunctureProjectionBaseChangeIso_fst]
  have hmap : ((baseChange (j₁).left).map (cylinderProjectionLift X V)).left ≫
      pullback.fst ((baseChange (p).left).obj ((cylinderNeighborhood X).obj V)).hom
        (j₁).left =
    pullback.fst ((cylinderNeighborhood X₁).obj ((baseChange (π).left).obj V)).hom
      (j₁).left ≫ (cylinderProjectionLift X V).left :=
    pullback.lift_fst _ _ _
  change ((baseChange (j₁).left).map (cylinderProjectionLift X V)).left ≫
      pullback.fst ((baseChange (p).left).obj ((cylinderNeighborhood X).obj V)).hom
        (j₁).left ≫ pullback.fst ((cylinderNeighborhood X).obj V).hom (p).left =
    pullback.fst ((cylinderNeighborhood X₁).obj ((baseChange (π).left).obj V)).hom (j₁).left ≫
      (SmoothSite.a1Map (CommRingCat.of k) ((restrictionProjection π).app V)).left
  rw [← Category.assoc, hmap, Category.assoc, cylinderProjectionLift_fst]

/-- Pulling the original zero lift through the actual square is the target
zero lift followed by the ambient cylinder comparison. -/
theorem zeroNeighborhoodLift_projection (V : EtaleSeparatedFiniteType X.left) :
    (baseChange (π).left).map (zeroNeighborhoodLift X V) ≫
        (contractionZeroProjectionBaseChangeIso X).hom.app ((cylinderNeighborhood X).obj V) =
      zeroNeighborhoodLift X₁ ((baseChange (π).left).obj V) ≫
        (baseChange (i₁).left).map (cylinderProjectionLift X V) := by
  let f := (baseChange (π).left).map (zeroNeighborhoodLift X V) ≫
    (contractionZeroProjectionBaseChangeIso X).hom.app ((cylinderNeighborhood X).obj V)
  let g := zeroNeighborhoodLift X₁ ((baseChange (π).left).obj V) ≫
    (baseChange (i₁).left).map (cylinderProjectionLift X V)
  have hmap₀ : ((baseChange (π).left).map (zeroNeighborhoodLift X V)).left ≫
      pullback.fst ((zeroNeighborhood X).obj V).hom (π).left =
    pullback.fst V.hom (π).left ≫ (zeroNeighborhoodLift X V).left :=
    pullback.lift_fst _ _ _
  have hmap₁ : ((baseChange (i₁).left).map (cylinderProjectionLift X V)).left ≫
      pullback.fst ((baseChange (p).left).obj ((cylinderNeighborhood X).obj V)).hom
        (i₁).left =
    pullback.fst ((cylinderNeighborhood X₁).obj ((baseChange (π).left).obj V)).hom
      (i₁).left ≫ (cylinderProjectionLift X V).left :=
    pullback.lift_fst _ _ _
  have hz₀ : (zeroNeighborhoodLift X V).left ≫
      pullback.fst ((cylinderNeighborhood X).obj V).hom (i₀).left =
    (SmoothSite.a1Section (CommRingCat.of k) ((toSmoothSite X).obj V) 0).left :=
    pullback.lift_fst _ _ _
  have hz₁ : (zeroNeighborhoodLift X₁ ((baseChange (π).left).obj V)).left ≫
      pullback.fst ((cylinderNeighborhood X₁).obj ((baseChange (π).left).obj V)).hom
        (i₁).left =
    (SmoothSite.a1Section (CommRingCat.of k)
      ((toSmoothSite X₁).obj ((baseChange (π).left).obj V)) 0).left :=
    pullback.lift_fst _ _ _
  have hs : f.left ≫ pullback.snd (pullback.snd ((cylinderNeighborhood X).obj V).hom
      (p).left) (i₁).left =
    g.left ≫ pullback.snd (pullback.snd ((cylinderNeighborhood X).obj V).hom
      (p).left) (i₁).left :=
    (MorphismProperty.Over.w f).trans (MorphismProperty.Over.w g).symm
  change f = g
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · change (((baseChange (π).left).map (zeroNeighborhoodLift X V)).left ≫
          ((contractionZeroProjectionBaseChangeIso X).hom.app
            ((cylinderNeighborhood X).obj V)).left) ≫
          pullback.fst (pullback.snd ((cylinderNeighborhood X).obj V).hom (p).left) (i₁).left ≫
          pullback.fst ((cylinderNeighborhood X).obj V).hom (p).left =
        ((zeroNeighborhoodLift X₁ ((baseChange (π).left).obj V)).left ≫
          ((baseChange (i₁).left).map (cylinderProjectionLift X V)).left) ≫
          pullback.fst (pullback.snd ((cylinderNeighborhood X).obj V).hom (p).left) (i₁).left ≫
          pullback.fst ((cylinderNeighborhood X).obj V).hom (p).left
      simp only [Category.assoc]
      rw [contractionZeroProjectionBaseChangeIso_fst]
      change ((baseChange (π).left).map (zeroNeighborhoodLift X V)).left ≫
          pullback.fst ((zeroNeighborhood X).obj V).hom (π).left ≫
          pullback.fst ((cylinderNeighborhood X).obj V).hom (i₀).left =
        (zeroNeighborhoodLift X₁ ((baseChange (π).left).obj V)).left ≫
          ((baseChange (i₁).left).map (cylinderProjectionLift X V)).left ≫
          pullback.fst ((baseChange (p).left).obj ((cylinderNeighborhood X).obj V)).hom
            (i₁).left ≫ pullback.fst ((cylinderNeighborhood X).obj V).hom (p).left
      rw [← Category.assoc ((baseChange (π).left).map (zeroNeighborhoodLift X V)).left,
        hmap₀, Category.assoc, hz₀,
        ← Category.assoc ((baseChange (i₁).left).map (cylinderProjectionLift X V)).left,
        hmap₁, Category.assoc,
        ← Category.assoc (zeroNeighborhoodLift X₁ ((baseChange (π).left).obj V)).left,
        hz₁, cylinderProjectionLift_fst]
      exact congrArg (fun f ↦ f.left)
        (SmoothSite.a1Section_naturality (CommRingCat.of k)
          ((restrictionProjection π).app V) 0).symm
    · change (f.left ≫
          pullback.fst (pullback.snd ((cylinderNeighborhood X).obj V).hom (p).left) (i₁).left) ≫
          pullback.snd ((cylinderNeighborhood X).obj V).hom (p).left =
        (g.left ≫
          pullback.fst (pullback.snd ((cylinderNeighborhood X).obj V).hom (p).left) (i₁).left) ≫
          pullback.snd ((cylinderNeighborhood X).obj V).hom (p).left
      rw [Category.assoc, pullback.condition, ← Category.assoc, hs,
        Category.assoc, ← pullback.condition, ← Category.assoc]
  · exact hs

end Motivic.FiniteEtaleSite
