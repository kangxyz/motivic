/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.A1BaseChange
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Products.ParameterProducts

/-! # The actual cylinder base-change comparison is natural in the original neighborhoods -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable (R : CommRingCat.{u}) (X : SmoothSite (Spec R))

/-- Naturality retains the original geometric maps of étale neighborhoods. -/
theorem a1BaseChangeIso_naturality {V W : EtaleSeparatedFiniteType X.left} (f : V ⟶ W) :
    (toSmoothSite (SmoothSite.a1Cylinder R X)).map
        ((baseChange (SmoothSite.a1Projection R X).left).map f) ≫
      (a1BaseChangeIso R X W).hom =
    (a1BaseChangeIso R X V).hom ≫ SmoothSite.a1Map R ((toSmoothSite X).map f) := by
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  all_goals
    simp [a1BaseChangeIso, SmoothSite.a1Map, SmoothSite.productMap,
      SmoothSite.productLift, SmoothSite.productFst, SmoothSite.productSnd,
      toSmoothSite, baseChange, Category.assoc]

/-- The natural comparison identifies actual base change with literal neighborhood cylinders. -/
def a1BaseChangeNatIso :
    baseChange (SmoothSite.a1Projection R X).left ⋙
        toSmoothSite (SmoothSite.a1Cylinder R X) ≅
      toSmoothSite X ⋙ SmoothSite.parameterProduct (SmoothSite.affineLine R) :=
  NatIso.ofComponents (a1BaseChangeIso R X) (fun f => a1BaseChangeIso_naturality R X f)

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
