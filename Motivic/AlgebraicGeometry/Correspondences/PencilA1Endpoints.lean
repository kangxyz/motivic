/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.SignedProductPencilEndpoints
public import Motivic.Cohomology.A1.Projection

/-! # Literal polynomial-pencil endpoints in the cohomological affine-line cylinder -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u
namespace Motivic.PencilA1Endpoints

variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))

/-- Both producers use the same polynomial-spectrum cylinder. -/
theorem relativeLineSite_eq_a1Cylinder :
    RelativeEndpointDiagram.relativeLineSite X = SmoothSite.a1Cylinder (.of k) X := rfl

/-- The actual evaluation graph is the consumer's actual affine-line section. -/
theorem endpointMorphism_eq_a1Section (a : k) :
    RelativeEndpointDiagram.endpointMorphism X a = SmoothSite.a1Section (.of k) X a := by
  apply MorphismProperty.Over.Hom.ext
  rfl

end Motivic.PencilA1Endpoints
