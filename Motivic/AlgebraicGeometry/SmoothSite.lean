/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.MorphismProperty.Comma

/-!
# Smooth separated finite-type schemes over a base

`SmoothSite S` is the actual full subcategory of schemes over `S` whose
structure morphisms are smooth, separated and quasi-compact. Smoothness implies
locally finite presentation, and hence locally finite type. Thus the final
quasi-compactness condition gives finite type in the convention of the pinned
mathlib API, which represents finite type by these two conditions separately.

Morphisms are all scheme morphisms over `S`, not only smooth morphisms.
This file constructs the underlying category of the smooth site. A topology,
finite correspondences and transfers are separate constructions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic

/-- Smooth separated finite-type structure morphisms. -/
abbrev smoothSeparatedFiniteType : MorphismProperty Scheme.{u} :=
  (@Smooth ⊓ @IsSeparated) ⊓ @QuasiCompact

instance smoothSeparatedFiniteType_isStableUnderBaseChange :
    smoothSeparatedFiniteType.{u}.IsStableUnderBaseChange where
  of_isPullback sq hg :=
    ⟨⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Smooth) sq hg.1.1,
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsSeparated) sq hg.1.2⟩,
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiCompact) sq hg.2⟩

/-- The actual category of smooth separated finite-type schemes over `S`. -/
abbrev SmoothSite (S : Scheme.{u}) := smoothSeparatedFiniteType.Over ⊤ S

namespace SmoothSite

variable {S : Scheme.{u}}

instance (X : SmoothSite S) : Smooth X.hom := X.prop.1.1

instance (X : SmoothSite S) : IsSeparated X.hom := X.prop.1.2

instance (X : SmoothSite S) : QuasiCompact X.hom := X.prop.2

/-- In particular, each structure map is locally of finite type. -/
theorem locallyOfFiniteType (X : SmoothSite S) : LocallyOfFiniteType X.hom :=
  inferInstance

/-- Finite type is the conjunction of local finite type and quasi-compactness. -/
theorem finiteType (X : SmoothSite S) :
    LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom :=
  ⟨inferInstance, inferInstance⟩

/-- Construct a smooth-site object from its actual structure morphism. -/
def mk {X : Scheme.{u}} (f : X ⟶ S) [Smooth f] [IsSeparated f] [QuasiCompact f] :
    SmoothSite S :=
  MorphismProperty.Over.mk ⊤ f ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩

@[simp]
theorem mk_left {X : Scheme.{u}} (f : X ⟶ S) [Smooth f] [IsSeparated f] [QuasiCompact f] :
    (mk f).left = X := rfl

@[simp]
theorem mk_hom {X : Scheme.{u}} (f : X ⟶ S) [Smooth f] [IsSeparated f] [QuasiCompact f] :
    (mk f).hom = f := rfl

/-- The base scheme itself is a smooth-site object over itself. -/
def base (S : Scheme.{u}) : SmoothSite S := mk (𝟙 S)

/-- Forget to the usual category of schemes over `S`. This functor is full and faithful. -/
abbrev forget (S : Scheme.{u}) : SmoothSite S ⥤ Over S :=
  MorphismProperty.Over.forget _ _ _

/-- Forget the base structure as well. -/
abbrev forgetScheme (S : Scheme.{u}) : SmoothSite S ⥤ Scheme.{u} :=
  forget S ⋙ Over.forget S

/-- Any scheme morphism commuting with the structure morphisms is a smooth-site morphism. -/
def homMk {X Y : SmoothSite S} (f : X.left ⟶ Y.left) (h : f ≫ Y.hom = X.hom) : X ⟶ Y :=
  MorphismProperty.Over.homMk f h

@[simp]
theorem homMk_left {X Y : SmoothSite S} (f : X.left ⟶ Y.left)
    (h : f ≫ Y.hom = X.hom) : (homMk f h).left = f := rfl

end SmoothSite

end Motivic
