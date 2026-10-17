/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.SmoothSiteParameterProducts

/-!
# Literal smooth parameter-product consumers

These checks retain the scheme universe and both coefficient-category
universes. They test the displayed product maps as well as pullback
preservation, Nisnevich continuity and preservation of sheaf conditions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Motivic Motivic.SmoothSite

universe u v w

variable {S : Scheme.{u}}

example (T X : SmoothSite S) :
    ((parameterProduct T).obj X).left = pullback X.hom T.hom := rfl

example (T : SmoothSite S) {X Y : SmoothSite S} (f : X ⟶ Y) :
    (parameterProduct T).map f = productMap f (𝟙 T) := rfl

example (T : SmoothSite S) {X Y : SmoothSite S} (f : X ⟶ Y) :
    (parameterProduct T).map f ≫ productFst Y T = productFst X T ≫ f := by
  simp

example (T : SmoothSite S) {X Y : SmoothSite S} (f : X ⟶ Y) :
    (parameterProduct T).map f ≫ productSnd Y T = productSnd X T := by
  simp

example (T : SmoothSite S) :
    PreservesLimitsOfShape WalkingCospan (parameterProduct T) := inferInstance

example (T : SmoothSite S) :
    (parameterProduct T).IsContinuous (nisnevichTopology S) (nisnevichTopology S) :=
  inferInstance

example (T : SmoothSite S) {A : Type w} [Category.{v} A]
    (P : (SmoothSite S)ᵒᵖ ⥤ A) (hP : Presheaf.IsSheaf (nisnevichTopology S) P) :
    Presheaf.IsSheaf (nisnevichTopology S) ((parameterProduct T).op ⋙ P) :=
  parameterProduct_op_comp_isSheaf T P hP

example {C : Type u} [Category.{v} C] [HasBinaryProducts C]
    (J : Precoverage C) [J.IsStableUnderBaseChange] [J.HasPullbacks] (T : C) :
    (prod.functor.flip.obj T).IsContinuous J.toGrothendieck J.toGrothendieck :=
  Functor.prodRight_isContinuous J T
