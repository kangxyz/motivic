/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.A1BaseChange
public import Motivic.Cohomology.A1.Basic

/-! # The original degree-zero projection coefficient isomorphism for HI sheaves -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable (R : CommRingCat.{u}) (X : SmoothSite (Spec R))
  (F : Sheaf (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1})

/-- On each genuine étale test object, the coefficient map is the original A1 projection
followed by restriction along the actual base-change/product comparison. -/
theorem a1RestrictionCoefficient_app (V : EtaleSeparatedFiniteType X.left) :
    (restrictionToDirectImage F (SmoothSite.a1Projection R X)).hom.app (op V) =
      _root_.Motivic.A1.projectionPullback R F.obj ((toSmoothSite X).obj V) ≫
        F.obj.map (a1BaseChangeIso R X V).hom.op := by
  change F.obj.map ((restrictionProjection (SmoothSite.a1Projection R X)).app V).op = _
  rw [← a1BaseChangeIso_hom_projection, op_comp, Functor.map_comp]
  rfl

/-- Original HI supplies the degree-zero sheaf iso, without any inverse-image coefficient iso. -/
theorem a1RestrictionCoefficient_isIso (hF : _root_.Motivic.A1.IsInvariant R F.obj) :
    IsIso (restrictionToDirectImage F (SmoothSite.a1Projection R X)) := by
  have happ (V : (EtaleSeparatedFiniteType X.left)ᵒᵖ) :
      IsIso ((restrictionToDirectImage F (SmoothSite.a1Projection R X)).hom.app V) := by
    let : IsIso (_root_.Motivic.A1.projectionPullback R F.obj ((toSmoothSite X).obj V.unop)) := hF _
    rw [a1RestrictionCoefficient_app R X F V.unop]
    infer_instance
  have : IsIso ((sheafToPresheaf (nisnevichTopology X.left) AddCommGrpCat.{u + 1}).map
      (restrictionToDirectImage F (SmoothSite.a1Projection R X))) :=
    NatIso.isIso_of_isIso_app (restrictionToDirectImage F (SmoothSite.a1Projection R X)).hom
  exact isIso_of_reflects_iso (restrictionToDirectImage F (SmoothSite.a1Projection R X))
    (sheafToPresheaf _ _)

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
