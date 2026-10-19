/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.ParameterProduct
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Pullbacks

/-! # Native small-site neighborhoods from actual smooth-site etale maps -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

variable {S : Scheme.{u}} (X B : SmoothSite S) (f : B ⟶ X) [Etale f.left]

/-- Regard the same actual etale morphism as an object of the native small site. -/
def ofSmoothMap : EtaleSeparatedFiniteType X.left :=
  MorphismProperty.Over.mk ⊤ f.left ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩

/-- The original smooth object and the native small-site object have identical
underlying schemes. -/
def ofSmoothMapIso : B ≅ (toSmoothSite X).obj (ofSmoothMap X B f) :=
  MorphismProperty.Over.isoMk (Iso.refl B.left) (by
    change 𝟙 B.left ≫ (f.left ≫ X.hom) = B.hom
    rw [Category.id_comp]
    exact MorphismProperty.Over.w f)

/-- The canonical comparison preserves the original base morphism. -/
@[reassoc] theorem ofSmoothMapIso_toBase :
    (ofSmoothMapIso X B f).hom ≫ toBase X (ofSmoothMap X B f) = f := by
  apply MorphismProperty.Over.Hom.ext
  change 𝟙 B.left ≫ f.left = f.left
  exact Category.id_comp _

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
