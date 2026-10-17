/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.BoundaryBasePencilSites
/-! # Actual smooth affine sites of the refined original square -/
set_option linter.hashCommand false
public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Hom
variable {S X Y A : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine A]
  (q : X ⟶ S) (p : Y ⟶ X) (a : A ⟶ X) (U : X.Opens) (V : S.Opens)
  [IsAffine (boundaryBaseSourceOpen q U V).toScheme] [IsAffine V.toScheme]
example : IsAffine (boundaryBaseOverlap q p a U V) := inferInstance
example [SmoothOfRelativeDimension 1 q] :
    SmoothOfRelativeDimension 1 (boundaryBaseSpecProjection q U V) := inferInstance
example {k : Type u} [Field k] (t : S ⟶ Spec (.of k)) [Smooth t] :
    Smooth (boundaryBaseFieldMap V t) := inferInstance
#print axioms boundaryBaseCoverInclusion_projective_smooth
#print axioms boundaryBaseRetainedTarget_projective_smooth
#print axioms boundaryBaseCoverInclusion_spec_projection
#print axioms boundaryBaseOverlap_affine_instance
end AlgebraicGeometry.Scheme.Hom
