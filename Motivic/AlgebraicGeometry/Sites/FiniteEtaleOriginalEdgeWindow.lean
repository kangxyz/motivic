/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleOriginalMapTransport
public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleOrdinaryEdgeWindow

/-! # Finite-window consequences for the original restriction map

The degree-zero coefficient isomorphism is a separate, explicit mathematical
hypothesis. It is not an inverse-image equivalence and does not assume strict
homotopy invariance. Higher vanishing refers to the actual right-derived direct image.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Motivic.FiniteEtaleSite
variable {B : Scheme.{u}} {X Y : SmoothSite B} (h : Y ⟶ X)
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology B) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (nisnevichTopology X.left) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (nisnevichTopology Y.left) AddCommGrpCat.{u + 1})]
  (F : Sheaf (SmoothSite.nisnevichTopology B) AddCommGrpCat.{u + 1})
  [IsIso (restrictionToDirectImage F h)]

/-- The finite window and the actual degree-zero coefficient iso imply bijectivity
of the original big-site restriction, with its original map direction. -/
theorem originalRestriction_bijective_of_rightDerived_window (N : ℕ)
    (hR : ∀ q : ℕ, 0 < q → q ≤ N →
      IsZero (((directImage h.left).rightDerived q).obj
        ((restrict Y AddCommGrpCat.{u + 1}).obj F))) :
    Function.Bijective
      ((SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology B) F N).map h.op) := by
  have hcoeff := ConcreteCategory.bijective_of_isIso
    (((SheafCohomology.presheafFunctor.{u + 1, u + 1, u, u + 1} (nisnevichTopology X.left) N).map
      (restrictionToDirectImage F h)).app (op (identityObject X)))
  have hedge := ordinaryEdgeMap_bijective_of_rightDerived_window h.left
    (identityObject X) ((restrict Y AddCommGrpCat.{u + 1}).obj F) N hR
  have hbase := ConcreteCategory.bijective_of_isIso
    ((SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1} (nisnevichTopology Y.left)
      ((restrict Y AddCommGrpCat.{u + 1}).obj F) N).map (baseChangeIdentityIso h).inv.op)
  have hcomp := (cohomologyAtBaseEquiv Y F N).symm.bijective.comp
    (hbase.comp (hedge.comp (hcoeff.comp (cohomologyAtBaseEquiv X F N).bijective)))
  convert hcomp using 1
  funext x
  exact originalRestriction_eq_transported_ordinaryEdgeMap h F N x

/-- The endpoint-free window gives injectivity of that same original restriction map. -/
theorem originalRestriction_injective_of_rightDerived_window (N : ℕ)
    (hR : ∀ q : ℕ, 0 < q → q < N →
      IsZero (((directImage h.left).rightDerived q).obj
        ((restrict Y AddCommGrpCat.{u + 1}).obj F))) :
    Function.Injective
      ((SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology B) F N).map h.op) := by
  have hcoeff := (ConcreteCategory.bijective_of_isIso
    (((SheafCohomology.presheafFunctor.{u + 1, u + 1, u, u + 1} (nisnevichTopology X.left) N).map
      (restrictionToDirectImage F h)).app (op (identityObject X)))).1
  have hedge := ordinaryEdgeMap_injective_of_rightDerived_window h.left
    (identityObject X) ((restrict Y AddCommGrpCat.{u + 1}).obj F) N hR
  have hbase := (ConcreteCategory.bijective_of_isIso
    ((SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1} (nisnevichTopology Y.left)
      ((restrict Y AddCommGrpCat.{u + 1}).obj F) N).map (baseChangeIdentityIso h).inv.op)).1
  have hcomp := (cohomologyAtBaseEquiv Y F N).symm.injective.comp
    (hbase.comp (hedge.comp (hcoeff.comp (cohomologyAtBaseEquiv X F N).injective)))
  convert hcomp using 1
  funext x
  exact originalRestriction_eq_transported_ordinaryEdgeMap h F N x

end Motivic.FiniteEtaleSite
