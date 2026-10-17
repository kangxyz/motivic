/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.BoundaryBasePuncturedSquare
/-! # Original target compatibility in the actual refined punctured square -/
set_option linter.hashCommand false
public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Hom
variable {S X Y A C T : Scheme.{u}} (q : X ⟶ S) (p : Y ⟶ X) (a : A ⟶ X)
  (U : X.Opens) (V : S.Opens) (π : C ⟶ S) (j : Y ⟶ C)
  (hj : j ≫ π = p ≫ q) (v : T ⟶ C) (φ : pullback p a ⟶ T)
  (hφ : φ ≫ v = pullback.fst p a ≫ j)
example : boundaryBaseOverlapTarget q p a U V π j hj v φ hφ ≫
    ((v ≫ π) ⁻¹ᵁ V).ι = boundaryBaseOverlapMap q p a U V ≫ φ :=
  boundaryBaseOverlapTarget_ι q p a U V π j hj v φ hφ
example : boundaryBaseOverlapTarget q p a U V π j hj v φ hφ ≫
    boundaryBaseRetainedTarget π V v =
      pullback.fst _ _ ≫ boundaryBaseCoverInclusion q p π j hj U V :=
  boundaryBaseOverlapTarget_inclusion q p a U V π j hj v φ hφ
#print axioms boundaryBaseOverlapMap
#print axioms boundaryBaseOverlapTarget
#print axioms boundaryBaseOverlapTarget_inclusion
end AlgebraicGeometry.Scheme.Hom
