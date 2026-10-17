/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleOriginalMapAtBase

/-! # Explicit transport of the genuine edge back to the original cohomology map -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
universe u
namespace Motivic.FiniteEtaleSite
variable {B : Scheme.{u}} {X Y : SmoothSite B} (h : Y ⟶ X)
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology B) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (nisnevichTopology X.left) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (nisnevichTopology Y.left) AddCommGrpCat.{u + 1})]

/-- The coefficient-map/edge composite, transported back, is exactly the original map. -/
theorem originalRestriction_eq_transported_ordinaryEdgeMap
    (F : Sheaf (SmoothSite.nisnevichTopology B) AddCommGrpCat.{u + 1})
    (n : ℕ) (x : SheafCohomology.H.{u + 1, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology B) F n X) :
    (SheafCohomology.presheaf (SmoothSite.nisnevichTopology B) F n).map h.op x =
      (cohomologyAtBaseEquiv Y F n).symm
        ((SheafCohomology.presheaf (nisnevichTopology Y.left)
          ((restrict Y AddCommGrpCat).obj F) n).map (baseChangeIdentityIso h).inv.op
          (ordinaryEdgeMap h.left (identityObject X) ((restrict Y AddCommGrpCat).obj F) n
            (((SheafCohomology.presheafFunctor (nisnevichTopology X.left) n).map
              (restrictionToDirectImage F h)).app (op (identityObject X))
                (cohomologyAtBaseEquiv X F n x)))) := by
  apply (cohomologyAtBaseEquiv Y F n).injective
  rw [AddEquiv.apply_symm_apply, ordinaryEdgeMap_atBase_originalRestriction]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    Iso.inv_hom_id, op_id, CategoryTheory.Functor.map_id]
  rfl

end Motivic.FiniteEtaleSite
