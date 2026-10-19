/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Pencils.FamilyMaps
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeEndpointSupportDiagram
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.Projection

/-! # Literal polynomial-pencil endpoints in the cohomological affine-line cylinder -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u
namespace AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram
open _root_.AlgebraicGeometry.Scheme.SmoothSite

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))

/-- The literal relative affine line as an actual smooth-site object. -/
abbrev relativeLineSite := SmoothSite.product X (AffineLineField.line k)

variable (a : k)

/-- The actual relative endpoint as a morphism of the smooth site. -/
def endpointMorphism : X ⟶ relativeLineSite X :=
  SmoothSite.homMk (endpoint X.hom a) (endpoint_base X.hom a)

end AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram

namespace AlgebraicGeometry.Scheme.SmoothSite.AffineLine.Endpoints
open _root_.AlgebraicGeometry.Scheme.Products

variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))

/-- Both producers use the same polynomial-spectrum cylinder. -/
theorem relativeLineSite_eq_a1Cylinder :
    RelativeEndpointDiagram.relativeLineSite X = a1Cylinder (.of k) X := rfl

/-- The actual evaluation graph is the consumer's actual affine-line section. -/
theorem endpointMorphism_eq_a1Section (a : k) :
    RelativeEndpointDiagram.endpointMorphism X a = a1Section (.of k) X a := by
  apply MorphismProperty.Over.Hom.ext
  rfl

end AlgebraicGeometry.Scheme.SmoothSite.AffineLine.Endpoints
