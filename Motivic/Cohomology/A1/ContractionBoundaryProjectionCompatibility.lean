/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.ContractionBoundaryProjection

/-! # Projection compatibility of the unchanged Laurent boundary map

The comparison is proved on the original Laurent representatives. All maps on
boundary sheaves are the actual cokernel and closed-adjunction maps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Motivic.FiniteEtaleSite

variable {k : Type u} [Field k] (X : SmoothSite (Spec (CommRingCat.of k)))
  (F : SheafWithTransfers.{u + 1} k)

local notation "X₁" => SmoothSite.a1Cylinder (CommRingCat.of k) X
local notation "π" => SmoothSite.a1Projection (CommRingCat.of k) X
local notation "p" => SmoothSite.a1Map (CommRingCat.of k) π
local notation "q" => SmoothSite.productMap π (𝟙 (SmoothSite.torus (CommRingCat.of k)))
local notation "j₀" => SmoothSite.contractionOpen (CommRingCat.of k) X
local notation "j₁" => SmoothSite.contractionOpen (CommRingCat.of k) X₁
local notation "i₀" => SmoothSite.a1Section (CommRingCat.of k) X 0
local notation "i₁" => SmoothSite.a1Section (CommRingCat.of k) X₁ 0
local notation "G" => Functor.obj (SheafWithTransfers.toSheaf k) F

/-- Every original Laurent representative satisfies the actual projection square,
including the original small-site test, cokernel projections, units and zero lifts. -/
theorem laurentToBoundary_projection (V : FiniteEtaleSite X.left) :
    (laurentToAmbientCokernel X F).app (op V) ≫
        (ambientCokernelToBoundary X F).app (op V) ≫
        (contractionBoundaryProjection X F).hom.app (op V) =
      (G).obj.map (SmoothSite.productMap ((restrictionProjection π).app V)
        (𝟙 (SmoothSite.torus (CommRingCat.of k)))).op ≫
        (laurentToAmbientCokernel X₁ F).app (op ((baseChange (π).left).obj V)) ≫
        (ambientCokernelToBoundary X₁ F).app (op ((baseChange (π).left).obj V)) := by
  let V₁ := (baseChange (π).left).obj V
  let E₀ : FiniteEtaleSite (X₁).left := (cylinderNeighborhood X).obj V
  let E₁ : FiniteEtaleSite (SmoothSite.a1Cylinder (CommRingCat.of k) X₁).left :=
    (cylinderNeighborhood X₁).obj V₁
  let R := cylinderProjectionLift X V
  let B₀ := zeroSectionBoundary X F
  let B₁ := zeroSectionBoundary X₁ F
  let c₀ := (cokernel.π (restrictionToDirectImage G j₀) ≫
    (imageAdjunction (i₀).left).unit.app (boundaryAmbientCokernel G j₀)).hom
  let c₁ := (cokernel.π (restrictionToDirectImage G j₁) ≫
    (imageAdjunction (i₁).left).unit.app (boundaryAmbientCokernel G j₁)).hom
  let μ := (contractionZeroProjectionBaseChangeIso X).hom.app E₀
  let ν := (contractionPunctureProjectionBaseChangeIso X).hom.app E₀
  let ν' := (toSmoothSite (SmoothSite.torusCylinder (CommRingCat.of k) X₁)).map ν
  let R' := (toSmoothSite (SmoothSite.torusCylinder (CommRingCat.of k) X₁)).map
    ((baseChange (j₁).left).map R)
  have hβ := (contractionBoundaryProjection X F).hom.naturality
    (zeroNeighborhoodLift X V).op
  change B₀.obj.map (zeroNeighborhoodLift X V).op ≫
      (contractionBoundaryProjection X F).hom.app (op V) =
    (contractionBoundaryProjection X F).hom.app (op ((zeroNeighborhood X).obj V)) ≫
      B₁.obj.map ((baseChange (π).left).map (zeroNeighborhoodLift X V)).op at hβ
  have hgen : c₀.app (op E₀) ≫
      (contractionBoundaryProjection X F).hom.app (op ((zeroNeighborhood X).obj V)) =
    (G).obj.map ((restrictionProjection q).app ((puncturedNeighborhood X).obj V)).op ≫
      (G).obj.map ν'.op ≫ c₁.app (op ((baseChange (p).left).obj E₀)) ≫ B₁.obj.map μ.op := by
    have h := congrArg (fun f ↦ f.hom.app (op E₀))
      (contractionBoundaryProjection_generator X F)
    change (cokernel.π (restrictionToDirectImage G j₀)).hom.app (op E₀) ≫
        ((imageAdjunction (i₀).left).unit.app (boundaryAmbientCokernel G j₀)).hom.app (op E₀) ≫
        (contractionBoundaryProjection X F).hom.app (op ((zeroNeighborhood X).obj V)) =
      ((G).obj.map ((restrictionProjection q).app ((puncturedNeighborhood X).obj V)).op ≫
        (G).obj.map ν'.op) ≫
        c₁.app (op ((baseChange (p).left).obj E₀)) ≫ B₁.obj.map μ.op at h
    simpa only [c₀, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      Category.assoc] using h
  have hz : B₁.obj.map μ.op ≫
      B₁.obj.map ((baseChange (π).left).map (zeroNeighborhoodLift X V)).op =
    B₁.obj.map ((baseChange (i₁).left).map R).op ≫
      B₁.obj.map (zeroNeighborhoodLift X₁ V₁).op := by
    rw [← Functor.map_comp, ← op_comp, zeroNeighborhoodLift_projection,
      op_comp, Functor.map_comp]
  have hc := c₁.naturality R.op
  change (G).obj.map R'.op ≫ c₁.app (op E₁) =
    c₁.app (op ((baseChange (p).left).obj E₀)) ≫
      B₁.obj.map ((baseChange (i₁).left).map R).op at hc
  have hp : (G).obj.map (puncturedProjection X V).op ≫
      (G).obj.map ((restrictionProjection q).app ((puncturedNeighborhood X).obj V)).op ≫
      (G).obj.map ν'.op ≫ (G).obj.map R'.op =
    (G).obj.map (SmoothSite.productMap ((restrictionProjection π).app V)
      (𝟙 (SmoothSite.torus (CommRingCat.of k)))).op ≫
      (G).obj.map (puncturedProjection X₁ V₁).op := by
    simp only [← Functor.map_comp, ← op_comp]
    simpa only [Category.assoc] using
      congrArg (fun f ↦ (G).obj.map f.op) (puncturedProjection_projection X V)
  have hL (Y : SmoothSite (Spec (CommRingCat.of k))) (W : FiniteEtaleSite Y.left) :
      (laurentToAmbientCokernel Y F).app (op W) ≫
          (ambientCokernelToBoundary Y F).app (op W) =
        (G).obj.map (puncturedProjection Y W).op ≫
          (cokernel.π
            (restrictionToDirectImage G (SmoothSite.contractionOpen (CommRingCat.of k) Y)) ≫
            (imageAdjunction (SmoothSite.a1Section (CommRingCat.of k) Y 0).left).unit.app
              (boundaryAmbientCokernel G (SmoothSite.contractionOpen (CommRingCat.of k) Y))).hom.app
                (op ((cylinderNeighborhood Y).obj W)) ≫
          (zeroSectionBoundary Y F).obj.map (zeroNeighborhoodLift Y W).op := by
    change (𝟙 _ ≫ (G).obj.map (puncturedProjection Y W).op ≫
        (cokernel.π (restrictionToDirectImage G
          (SmoothSite.contractionOpen (CommRingCat.of k) Y))).hom.app
            (op ((cylinderNeighborhood Y).obj W))) ≫
        (((imageAdjunction (SmoothSite.a1Section (CommRingCat.of k) Y 0).left).unit.app
          (boundaryAmbientCokernel G (SmoothSite.contractionOpen (CommRingCat.of k) Y))).hom.app
            (op ((cylinderNeighborhood Y).obj W)) ≫
          (zeroSectionBoundary Y F).obj.map (zeroNeighborhoodLift Y W).op) = _
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      Category.id_comp, Category.assoc]
  rw [← Category.assoc, hL, hL]
  change ((G).obj.map (puncturedProjection X V).op ≫ c₀.app (op E₀) ≫
      B₀.obj.map (zeroNeighborhoodLift X V).op) ≫
      (contractionBoundaryProjection X F).hom.app (op V) =
    (G).obj.map (SmoothSite.productMap ((restrictionProjection π).app V)
      (𝟙 (SmoothSite.torus (CommRingCat.of k)))).op ≫
      (G).obj.map (puncturedProjection X₁ V₁).op ≫
      c₁.app (op E₁) ≫ B₁.obj.map (zeroNeighborhoodLift X₁ V₁).op
  simp only [Category.assoc]
  rw [hβ, ← Category.assoc (c₀.app (op E₀)), hgen]
  simp only [Category.assoc]
  rw [hz, ← Category.assoc (c₁.app (op ((baseChange (p).left).obj E₀))), ← hc]
  simpa only [Category.assoc] using congrArg
    (fun f ↦ f ≫ c₁.app (op E₁) ≫ B₁.obj.map (zeroNeighborhoodLift X₁ V₁).op) hp

/-- The actual projection map commutes with the canonical boundary map from
the unchanged contraction. No epimorphism or purity input is required. -/
theorem contractionToBoundary_projection (hF : F.obj.IsA1Invariant) :
    contractionToBoundary X F hF ≫ contractionBoundaryProjection X F =
      restrictionToDirectImage
          ((SheafWithTransfers.toSheaf k).obj (SheafWithTransfers.contraction F hF)) π ≫
        (directImage (π).left).map (contractionToBoundary X₁ F hF) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  ext c
  obtain ⟨s, rfl⟩ := PresheafWithTransfers.toContraction_surjective F.obj
    (Cor.mk ((toSmoothSite X).obj V.unop)) c
  change (contractionBoundaryProjection X F).hom.app V
      ((contractionToBoundary X F hF).hom.app V
        ((PresheafWithTransfers.toContraction F.obj).hom.app
          (op (Cor.mk ((toSmoothSite X).obj V.unop))) s)) =
    (contractionToBoundary X₁ F hF).hom.app (op ((baseChange (π).left).obj V.unop))
      (PresheafWithTransfers.transfer (PresheafWithTransfers.contraction F.obj)
        ((Cor.graphFunctor k).map ((restrictionProjection π).app V.unop))
        ((PresheafWithTransfers.toContraction F.obj).hom.app
          (op (Cor.mk ((toSmoothSite X).obj V.unop))) s))
  rw [PresheafWithTransfers.contraction_graph_apply]
  have h₀ := ConcreteCategory.congr_hom
    (congr_app (toContraction_contractionToBoundaryPresheaf X F) V) s
  have h₁ := ConcreteCategory.congr_hom
    (congr_app (toContraction_contractionToBoundaryPresheaf X₁ F)
      (op ((baseChange (π).left).obj V.unop)))
    ((G).obj.map (SmoothSite.productMap ((restrictionProjection π).app V.unop)
      (𝟙 (SmoothSite.torus (CommRingCat.of k)))).op s)
  exact (congrArg ((contractionBoundaryProjection X F).hom.app V) h₀).trans
    ((ConcreteCategory.congr_hom (laurentToBoundary_projection X F V.unop) s).trans h₁.symm)

end Motivic.FiniteEtaleSite
