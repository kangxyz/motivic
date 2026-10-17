/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.SmoothSiteAffineCoordinates
public import Motivic.AlgebraicGeometry.SmoothSiteIntegralAffineSheafIso
public import Motivic.AlgebraicGeometry.SmoothSiteUnits
public import Motivic.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorus

/-! # The actual ordinary global-unit map from the original torus representable -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent
open Motivic.AffineTorusPolynomialPresentation Motivic.SmoothSiteAffineCoordinates
open Polynomial.BoundaryOneRationalFunctions

universe u

namespace Motivic.SmoothSiteTorusDivisor

variable {k : Type u} [Field k]
attribute [local instance] sectionsAlgebra

/-- Precomposition with the genuine canonical affine-coordinate isomorphism. -/
def affineCycleCoordinates (X : SmoothSite (Spec (.of k))) [IsAffine X.left] :
    (Cor.mk X ⟶ Cor.mk (SmoothSite.torus (.of k))) →+
      FiniteCorrespondence (baseMap k Γ(X.left, ⊤)) (laurentProjection (.of k)) :=
  Preadditive.leftComp (Cor.mk (SmoothSite.torus (.of k)))
    ((Cor.graphFunctor k).map (affineIso X).hom)

/-- No choice of affine coordinates alters the original graph restriction. -/
theorem affineCycleCoordinates_natural
    {X Y : SmoothSite (Spec (.of k))} [IsAffine X.left] [IsAffine Y.left]
    (f : X ⟶ Y) (z : Cor.mk Y ⟶ Cor.mk (SmoothSite.torus (.of k))) :
    affineRestriction (sectionsMap f) (affineCycleCoordinates Y z) =
      affineCycleCoordinates X ((Cor.graphFunctor k).map f ≫ z) := by
  change (Cor.graphFunctor k).map (affineMorphism (sectionsMap f)) ≫
      ((Cor.graphFunctor k).map (affineIso Y).hom ≫ z) =
    (Cor.graphFunctor k).map (affineIso X).hom ≫ ((Cor.graphFunctor k).map f ≫ z)
  rw [← Category.assoc, ← Functor.map_comp, affineIso_naturality,
    Functor.map_comp, Category.assoc]

/-- Signed constant coefficient of the original cycle, in its actual global units. -/
def affineNorm (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left] :
    (Cor.mk X ⟶ Cor.mk (SmoothSite.torus (.of k))) →+ Additive (Γ(X.left, ⊤))ˣ :=
  signedValueHom.toAdditive.comp (cycleRationalFunction.comp (affineCycleCoordinates X))

/-- The actual norm is natural for every ordinary map between integral affine sources. -/
theorem affineNorm_natural
    {X Y : SmoothSite (Spec (.of k))} [IsAffine X.left] [IsAffine Y.left]
    [IsIntegral X.left] [IsIntegral Y.left] (f : X ⟶ Y)
    (z : Cor.mk Y ⟶ Cor.mk (SmoothSite.torus (.of k))) :
    affineNorm X ((Cor.graphFunctor k).map f ≫ z) =
      (Units.map f.left.appTop.hom.toMonoidHom).toAdditive (affineNorm Y z) := by
  have hc := affineCycleCoordinates_natural f z
  have hr := cycleRationalFunction_natural (k := k)
    (sectionsMap f) (affineCycleCoordinates Y z)
  have he := (congrArg (cycleRationalFunction (k := k) (R := Γ(X.left, ⊤))) hc.symm).trans hr
  have hs := congrArg (signedValueHom (R := Γ(X.left, ⊤))).toAdditive he
  have ht := congrArg Additive.ofMul (signedValueHom_natural (sectionsMap f).toRingHom
    (cycleRationalFunction (k := k) (affineCycleCoordinates Y z)).toMul)
  exact hs.trans ht

/-- The original first torus-power target is retained through its canonical actual isomorphism. -/
def affinePowerOneNorm (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left] :
    (Cor.mk X ⟶ Cor.mk (SmoothSite.torusPower (.of k) 1)) →+ Additive (Γ(X.left, ⊤))ˣ :=
  (affineNorm X).comp (Preadditive.rightComp (Cor.mk X)
    ((Cor.graphFunctor k).map (SmoothSite.torusPowerOneIso (.of k)).hom))

/-- Ordinary naturality for the project's literal first torus-power representable. -/
theorem affinePowerOneNorm_natural
    {X Y : SmoothSite (Spec (.of k))} [IsAffine X.left] [IsAffine Y.left]
    [IsIntegral X.left] [IsIntegral Y.left] (f : X ⟶ Y)
    (z : Cor.mk Y ⟶ Cor.mk (SmoothSite.torusPower (.of k) 1)) :
    affinePowerOneNorm X ((Cor.graphFunctor k).map f ≫ z) =
      (Units.map f.left.appTop.hom.toMonoidHom).toAdditive (affinePowerOneNorm Y z) := by
  change affineNorm X (((Cor.graphFunctor k).map f ≫ z) ≫
      (Cor.graphFunctor k).map (SmoothSite.torusPowerOneIso (.of k)).hom) = _
  rw [Category.assoc]
  exact affineNorm_natural f _

open PresheafWithTransfers

/-- The genuine signed-unit map in the coefficient universe of the original motivic complex. -/
def largeAffineNorm (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left] :
    ((toPresheaf k).obj (torusRepresentable k 1)).obj (op X) ⟶
      (SmoothSite.largeUnitsPresheaf (Spec (.of k))).obj (op X) :=
  AddCommGrpCat.ofHom {
    toFun z := ULift.up (affinePowerOneNorm X z.down)
    map_zero' := by change ULift.up (affinePowerOneNorm X 0) = ULift.up 0; rw [map_zero]
    map_add' z w := by
      change ULift.up (affinePowerOneNorm X (z.down + w.down)) =
        ULift.up (affinePowerOneNorm X z.down + affinePowerOneNorm X w.down)
      rw [map_add] }

/-- The constructed maps form a natural transformation on the genuine integral-affine subsite. -/
def integralAffineNorm :
    (SmoothSite.integralAffineInclusion k).op ⋙ (toPresheaf k).obj (torusRepresentable k 1) ⟶
      (SmoothSite.integralAffineInclusion k).op ⋙
        SmoothSite.largeUnitsPresheaf (Spec (.of k)) where
  app X := by
    let : IsAffine X.unop.obj.left := X.unop.property.1
    let : IsIntegral X.unop.obj.left := X.unop.property.2
    exact largeAffineNorm X.unop.obj
  naturality {X Y} f := by
    let : IsAffine X.unop.obj.left := X.unop.property.1
    let : IsIntegral X.unop.obj.left := X.unop.property.2
    let : IsAffine Y.unop.obj.left := Y.unop.property.1
    let : IsIntegral Y.unop.obj.left := Y.unop.property.2
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro z
    change ULift.up (affinePowerOneNorm Y.unop.obj
      ((Cor.graphFunctor k).map f.unop.hom ≫ z.down)) =
      ULift.up ((Units.map f.unop.hom.left.appTop.hom.toMonoidHom).toAdditive
        (affinePowerOneNorm X.unop.obj z.down))
    exact congrArg ULift.up (affinePowerOneNorm_natural f.unop.hom z.down)

/-- Ordinary Nisnevich descent extends the actual divisor-unit map to every smooth scheme. -/
def norm : (toPresheaf k).obj (torusRepresentable k 1) ⟶
    SmoothSite.largeUnitsPresheaf (Spec (.of k)) :=
  SmoothSite.extendIntegralAffineHom k (G := SmoothSite.largeUnitsSheaf (Spec (.of k)))
    integralAffineNorm

/-- On every integral affine source, the descended map is the constructed original-cycle map. -/
theorem norm_app (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left] :
    norm.app (op X) = largeAffineNorm X := by
  have h := Functor.IsCoverDense.sheafHom_restrict_eq
    (G := SmoothSite.integralAffineInclusion k)
    (ℱ' := SmoothSite.largeUnitsSheaf (Spec (.of k))) integralAffineNorm
  exact congrArg (fun η => η.app (op ⟨X, inferInstance, inferInstance⟩)) h

end Motivic.SmoothSiteTorusDivisor
