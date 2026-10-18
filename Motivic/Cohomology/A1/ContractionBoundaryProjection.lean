/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.ContractionBoundaryProjectionGeometry
public import Motivic.Cohomology.A1.ContractionBoundarySheaf
public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleImageExact

/-! # The actual projection morphism on zero-section boundary sheaves

This constructs a morphism using cokernels, genuine adjunction units and literal
commuting product squares. It does not assert a smooth inverse-image coefficient
isomorphism or invertibility of the contraction boundary.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Motivic.FiniteEtaleSite

variable {k : Type u} [Field k] (X : SmoothSite (Spec (CommRingCat.of k)))

local notation "X₁" => SmoothSite.a1Cylinder (CommRingCat.of k) X
local notation "π" => SmoothSite.a1Projection (CommRingCat.of k) X
local notation "p" => SmoothSite.a1Map (CommRingCat.of k) π
local notation "q" => SmoothSite.productMap π (𝟙 (SmoothSite.torus (CommRingCat.of k)))
local notation "j₀" => SmoothSite.contractionOpen (CommRingCat.of k) X
local notation "j₁" => SmoothSite.contractionOpen (CommRingCat.of k) X₁
local notation "i₀" => SmoothSite.a1Section (CommRingCat.of k) X 0
local notation "i₁" => SmoothSite.a1Section (CommRingCat.of k) X₁ 0

/-- The direct images of the actual punctured product square commute. -/
def contractionPunctureProjectionDirectImageIso :
    directImage (q).left ⋙ directImage (j₀).left ≅
      directImage (j₁).left ⋙ directImage (p).left := by
  letI : (baseChange (q).left).IsContinuous
      (nisnevichTopology (SmoothSite.torusCylinder (CommRingCat.of k) X).left)
      (nisnevichTopology (SmoothSite.torusCylinder (CommRingCat.of k) X₁).left) :=
    baseChange_isContinuous (q).left
  have := Functor.isContinuous_comp (baseChange (j₀).left) (baseChange (q).left)
    (nisnevichTopology (X₁).left)
    (nisnevichTopology (SmoothSite.torusCylinder (CommRingCat.of k) X).left)
    (nisnevichTopology (SmoothSite.torusCylinder (CommRingCat.of k) X₁).left)
  have := Functor.isContinuous_comp (baseChange (p).left) (baseChange (j₁).left)
    (nisnevichTopology (X₁).left)
    (nisnevichTopology (SmoothSite.a1Cylinder (CommRingCat.of k) X₁).left)
    (nisnevichTopology (SmoothSite.torusCylinder (CommRingCat.of k) X₁).left)
  exact Functor.sheafPushforwardContinuousIso
    (contractionPunctureProjectionBaseChangeIso X).symm AddCommGrpCat.{u + 1}
    (nisnevichTopology (X₁).left)
    (nisnevichTopology (SmoothSite.torusCylinder (CommRingCat.of k) X₁).left)

/-- The direct images of the actual zero-section product square commute. -/
def contractionZeroProjectionDirectImageIso :
    directImage (i₁).left ⋙ directImage (p).left ≅
      directImage (π).left ⋙ directImage (i₀).left := by
  have := Functor.isContinuous_comp (baseChange (p).left) (baseChange (i₁).left)
    (nisnevichTopology (X₁).left)
    (nisnevichTopology (SmoothSite.a1Cylinder (CommRingCat.of k) X₁).left)
    (nisnevichTopology (X₁).left)
  have := Functor.isContinuous_comp (baseChange (i₀).left) (baseChange (π).left)
    (nisnevichTopology (X₁).left) (nisnevichTopology X.left) (nisnevichTopology (X₁).left)
  exact Functor.sheafPushforwardContinuousIso
    (contractionZeroProjectionBaseChangeIso X).symm AddCommGrpCat.{u + 1}
    (nisnevichTopology (X₁).left) (nisnevichTopology (X₁).left)

variable (F : SheafWithTransfers.{u + 1} k)

local notation "G" => Functor.obj (SheafWithTransfers.toSheaf k) F

/-- Original punctured sections pull back along the literal projection square. -/
def contractionPuncturedProjectionMap :
    (directImage (j₀).left).obj
      ((restrict (SmoothSite.torusCylinder (CommRingCat.of k) X) AddCommGrpCat).obj G) ⟶
      (directImage (p).left).obj
        ((directImage (j₁).left).obj
          ((restrict (SmoothSite.torusCylinder (CommRingCat.of k) X₁) AddCommGrpCat).obj G)) :=
  (directImage (j₀).left).map (restrictionToDirectImage G q) ≫
    (contractionPunctureProjectionDirectImageIso X).hom.app
      ((restrict (SmoothSite.torusCylinder (CommRingCat.of k) X₁) AddCommGrpCat).obj G)

/-- The punctured projection preserves the original ambient restriction relation. -/
theorem contractionPuncturedProjectionMap_restriction :
    restrictionToDirectImage G j₀ ≫ contractionPuncturedProjectionMap X F =
      restrictionToDirectImage G p ≫
        (directImage (p).left).map (restrictionToDirectImage G j₁) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext E
  change (G).obj.map ((restrictionProjection j₀).app E.unop).op ≫
      ((G).obj.map ((restrictionProjection q).app ((baseChange (j₀).left).obj E.unop)).op ≫
        (G).obj.map ((toSmoothSite (SmoothSite.torusCylinder (CommRingCat.of k) X₁)).map
          ((contractionPunctureProjectionBaseChangeIso X).hom.app E.unop)).op) =
    (G).obj.map ((restrictionProjection p).app E.unop).op ≫
      (G).obj.map ((restrictionProjection j₁).app ((baseChange (p).left).obj E.unop)).op
  simp only [← Functor.map_comp, ← op_comp]
  congr 2
  apply MorphismProperty.Over.Hom.ext
  change ((contractionPunctureProjectionBaseChangeIso X).hom.app E.unop).left ≫
      pullback.fst (pullback.snd E.unop.hom (j₀).left) (q).left ≫
      pullback.fst E.unop.hom (j₀).left =
    pullback.fst (pullback.snd E.unop.hom (p).left) (j₁).left ≫
      pullback.fst E.unop.hom (p).left
  exact contractionPunctureProjectionBaseChangeIso_fst X E.unop

/-- The original ambient sheaf cokernel maps to the direct image of the product
ambient cokernel. No preservation of cokernels by direct image is assumed. -/
def contractionAmbientProjectionMap :
    boundaryAmbientCokernel G j₀ ⟶ (directImage (p).left).obj (boundaryAmbientCokernel G j₁) :=
  cokernel.desc (restrictionToDirectImage G j₀)
    (contractionPuncturedProjectionMap X F ≫
      (directImage (p).left).map (cokernel.π (restrictionToDirectImage G j₁))) (by
        rw [← Category.assoc, contractionPuncturedProjectionMap_restriction, Category.assoc,
          ← Functor.map_comp, cokernel.condition, Functor.map_zero, comp_zero])

/-- The ambient map retains the actual original punctured quotient projection. -/
@[reassoc (attr := simp)]
theorem contractionAmbientProjectionMap_π :
    cokernel.π (restrictionToDirectImage G j₀) ≫ contractionAmbientProjectionMap X F =
      contractionPuncturedProjectionMap X F ≫
        (directImage (p).left).map (cokernel.π (restrictionToDirectImage G j₁)) :=
  cokernel.π_desc _ _ _

/-- The genuine projection morphism of zero-section boundary sheaves, defined as
the mate of ambient pullback followed by the actual closed inverse-image unit. -/
def contractionBoundaryProjection :
    zeroSectionBoundary X F ⟶ (directImage (π).left).obj (zeroSectionBoundary X₁ F) :=
  ((imageAdjunction (i₀).left).homEquiv _ _).symm
    (contractionAmbientProjectionMap X F ≫
      (directImage (p).left).map
        ((imageAdjunction (i₁).left).unit.app (boundaryAmbientCokernel G j₁)) ≫
      (contractionZeroProjectionDirectImageIso X).hom.app (zeroSectionBoundary X₁ F))

/-- The adjoint equation records the unchanged ambient map and inverse-image units. -/
theorem contractionBoundaryProjection_unit :
    (imageAdjunction (i₀).left).unit.app (boundaryAmbientCokernel G j₀) ≫
        (directImage (i₀).left).map (contractionBoundaryProjection X F) =
      contractionAmbientProjectionMap X F ≫
        (directImage (p).left).map
          ((imageAdjunction (i₁).left).unit.app (boundaryAmbientCokernel G j₁)) ≫
        (contractionZeroProjectionDirectImageIso X).hom.app (zeroSectionBoundary X₁ F) := by
  change (imageAdjunction (i₀).left).homEquiv _ _ (contractionBoundaryProjection X F) = _
  exact Equiv.apply_symm_apply _ _

/-- The actual projection sends every original punctured-section generator to
its literal product pullback followed by the target quotient and closed unit. -/
theorem contractionBoundaryProjection_generator :
    cokernel.π (restrictionToDirectImage G j₀) ≫
        (imageAdjunction (i₀).left).unit.app (boundaryAmbientCokernel G j₀) ≫
        (directImage (i₀).left).map (contractionBoundaryProjection X F) =
      contractionPuncturedProjectionMap X F ≫
        (directImage (p).left).map
          (cokernel.π (restrictionToDirectImage G j₁) ≫
            (imageAdjunction (i₁).left).unit.app (boundaryAmbientCokernel G j₁)) ≫
        (contractionZeroProjectionDirectImageIso X).hom.app (zeroSectionBoundary X₁ F) := by
  rw [contractionBoundaryProjection_unit, ← Category.assoc,
    contractionAmbientProjectionMap_π]
  simp only [Functor.map_comp, Category.assoc]

end Motivic.FiniteEtaleSite
