/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.GraphScalar
public import Aglib.AlgebraicGeometry.Modules.Locality.Sections
public import Aglib.AlgebraicGeometry.Modules.Pullback.FlatMorphism

/-!
# Regularity of the original arbitrary-frame marked graph scalar

The supplied target frame need not be the polynomial coordinate frame.
Its inclusion is monic, and flat pullback preserves that original monomorphism.
The full marked ring can be nonreduced.


Intended upstream module: `Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.GraphRegular`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.AffineMarkedGraphRegular`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- A monic endomorphism of the structure module has a regular value on one. -/
theorem isSMulRegular_unitEnd_app_one {X : Scheme.{u}}
    (θ : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶
      SheafOfModules.unit X.ringCatSheaf) [Mono θ] :
    IsSMulRegular Γ(X, ⊤)
      (show Γ(X, ⊤) from Hom.app θ ⊤ (1 : Γ(X, ⊤))) := by
  intro x y h
  apply moduleHom_app_injective θ ⊤
  let F : Γ(X, ⊤) → Γ(X, ⊤) := fun t => Hom.app θ ⊤ t
  let a : Γ(X, ⊤) := Hom.app θ ⊤ (1 : Γ(X, ⊤))
  have hx := Hom.app_smul θ x (1 : Γ(X, ⊤))
  have hy := Hom.app_smul θ y (1 : Γ(X, ⊤))
  change F (x * 1) = x * a at hx
  change F (y * 1) = y * a at hy
  rw [mul_one] at hx hy
  change F x = F y
  rw [hx, hy]
  exact (mul_comm _ _).trans (h.trans (mul_comm _ _))

/-- The actual pullback of a monic structure-module endomorphism along a
flat map gives a regular scalar under the original sections map. -/
theorem isSMulRegular_unitEnd_app_one_flat_pullback {X W : Scheme.{u}}
    (b : W ⟶ X) [Flat b]
    (θ : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶
      SheafOfModules.unit X.ringCatSheaf) [Mono θ] :
    IsSMulRegular Γ(W, ⊤) (b.appTop (Hom.app θ ⊤ (1 : Γ(X, ⊤)))) := by
  have : Mono ((Scheme.Modules.pullback b).map θ) := mono_pullback_of_flat_all b θ
  have : Mono (Scheme.Hom.unitEndomorphismPullback b θ) := by
    unfold Scheme.Hom.unitEndomorphismPullback
    exact mono_comp _ _
  have h := isSMulRegular_unitEnd_app_one (Scheme.Hom.unitEndomorphismPullback b θ)
  rwa [Scheme.Hom.unitEndomorphismPullback_app_one] at h

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Hom

open Modules Modules.Invertible

/-- Any given target graph frame has regular scalar on the original marked
product after base change of the original flat parameter map. -/
theorem boundaryProductMap_frame_scalar_regular
    {S X Y Z : Scheme.{u}} (q : X ⟶ S) (p : Y ⟶ X) [Flat p] (z : Z ⟶ X)
    (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
      idealModule (boundaryGraphTarget q z)) :
    IsSMulRegular Γ(pullback (p ≫ q) (z ≫ q), ⊤)
      ((boundaryProductMap q p z).appTop
        (Modules.Hom.app (e.hom ≫ idealInclusion (boundaryGraphTarget q z)) ⊤
          (1 : Γ(pullback q (z ≫ q), ⊤)))) := by
  have : Mono (idealInclusion (boundaryGraphTarget q z)) :=
    idealInclusionMono (boundaryGraphTarget q z)
  have : Mono (e.hom ≫ idealInclusion (boundaryGraphTarget q z)) := mono_comp _ _
  exact Modules.isSMulRegular_unitEnd_app_one_flat_pullback (boundaryProductMap q p z) _

/-- The exact marked scalar of the original compactification boundary frame
is regular. No equality with a chosen polynomial generator is asserted. -/
theorem relativeCompactificationBoundaryFrame_scalar_regular
    {S X Y Z C : Scheme.{u}} (q : X ⟶ S) [IsSeparated q]
    [SmoothOfRelativeDimension 1 q] (qC : C ⟶ S) [IsSeparated qC]
    (j : Y ⟶ C) [IsOpenImmersion j] (p : Y ⟶ X) [Flat p]
    (hq : j ≫ qC = p ≫ q) (z : Z ⟶ X) (s : Z ⟶ Y) (h : s ≫ p = z)
    (H : IsPullback s (𝟙 _) p z)
    (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
      idealModule (boundaryGraphTarget q z)) :
    IsSMulRegular Γ(pullback (j ≫ qC) (s ≫ j ≫ qC), ⊤)
      (show Γ(pullback (j ≫ qC) (s ≫ j ≫ qC), ⊤) from Modules.Hom.app
        ((relativeCompactificationBoundaryFrame q qC j p hq z s h H e).hom ≫
          Modules.Hom.pullbackToUnit (idealInclusion (compactificationGraph qC j))
            (graphBoundaryRestriction qC j s)) ⊤
          (1 : Γ(pullback (j ≫ qC) (s ≫ j ≫ qC), ⊤))) := by
  have : Mono (idealInclusion (boundaryGraphTarget q z)) :=
    idealInclusionMono (boundaryGraphTarget q z)
  have : Mono (e.hom ≫ idealInclusion (boundaryGraphTarget q z)) := mono_comp _ _
  rw [relativeCompactificationBoundaryFrame_scalar]
  exact Modules.isSMulRegular_unitEnd_app_one_flat_pullback
    ((relativeBoundaryProductIso q qC j p hq z s h).hom ≫ boundaryProductMap q p z) _

end AlgebraicGeometry.Scheme.Hom
