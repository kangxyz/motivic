/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.BaseChange
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.ForgetBase
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.ScalarExtension.Finite.Basic

/-! # Original field base change and finite scalar extension

The comparison is the identity on the original pullback scheme. Only the two
expressions for its structure map differ, by the pullback condition.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  [Module.Finite k L] [Algebra.IsSeparable k L]

/-- Forgetting the ground field of the actual base change gives the scalar object,
by the identity on its underlying pullback scheme. -/
def fieldBaseChangeFiniteScalarIso (X : SmoothSite (Spec (.of k))) :
    (finiteSeparableForgetBase k L).obj ((fieldBaseChange (algebraMap k L)).obj X) ≅
      finiteScalarExtension (E := L) X :=
  MorphismProperty.Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ (pullback.fst X.hom (finiteSeparableBaseMap k L) ≫ X.hom) =
      pullback.snd X.hom (finiteSeparableBaseMap k L) ≫ finiteSeparableBaseMap k L
    simpa only [Category.id_comp] using
      (pullback.condition (f := X.hom) (g := finiteSeparableBaseMap k L)))

@[simp]
theorem fieldBaseChangeFiniteScalarIso_hom_left (X : SmoothSite (Spec (.of k))) :
    (fieldBaseChangeFiniteScalarIso (L := L) X).hom.left = 𝟙 _ := rfl

@[simp]
theorem fieldBaseChangeFiniteScalarIso_inv_left (X : SmoothSite (Spec (.of k))) :
    (fieldBaseChangeFiniteScalarIso (L := L) X).inv.left = 𝟙 _ := rfl

/-- The comparison intertwines every original geometric arrow, including cylinder,
zero-section and Laurent arrows, without choosing replacement models. -/
@[reassoc]
theorem fieldBaseChangeFiniteScalarIso_inv_naturality
    {X Y : SmoothSite (Spec (.of k))} (f : X ⟶ Y) :
    (fieldBaseChangeFiniteScalarIso (L := L) X).inv ≫
        (finiteSeparableForgetBase k L).map ((fieldBaseChange (algebraMap k L)).map f) =
      finiteScalarMap (E := L) f ≫ (fieldBaseChangeFiniteScalarIso (L := L) Y).inv := by
  apply MorphismProperty.Over.Hom.ext
  change 𝟙 _ ≫ _ = _ ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id]
  rfl

/-- The projection from the forgotten field base change is the original first projection. -/
def fieldBaseChangeForgetProjection (X : SmoothSite (Spec (.of k))) :
    (finiteSeparableForgetBase k L).obj ((fieldBaseChange (algebraMap k L)).obj X) ⟶ X :=
  homMk (pullback.fst X.hom (finiteSeparableBaseMap k L))
    (pullback.condition (f := X.hom) (g := finiteSeparableBaseMap k L))

/-- Both presentations preserve the literal original scalar projection. -/
@[reassoc]
theorem fieldBaseChangeFiniteScalarIso_inv_projection (X : SmoothSite (Spec (.of k))) :
    (fieldBaseChangeFiniteScalarIso (L := L) X).inv ≫
        fieldBaseChangeForgetProjection (L := L) X = finiteScalarProjection (E := L) X := by
  apply MorphismProperty.Over.Hom.ext
  exact Category.id_comp _

end AlgebraicGeometry.Scheme.SmoothSite
