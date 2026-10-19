/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Cohomology.FieldEvaluation
public import Motivic.Transfers.Sheaf.Basic

/-!
# Direct consumers of ordinary cohomology vanishing at the base field

These tests use the standard Ext instance, arbitrary fields, arbitrary ordinary
coefficients, and the original larger-universe sheaves with transfers. The
evaluated site object is the field's own base, and the classes are literal Ext
classes from the existing free section-representing sheaf.
-/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

namespace MotivicTest.Cohomology.SheafCohomologyFieldEvaluation

variable (k : Type u) [Field k]

local instance : HasExt.{u + 2}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}) :=
  HasExt.standard _

/-- The existing free section-representing sheaf, with its original universe, is projective. -/
theorem actual_base_free_sheaf_projective :
    Projective (_root_.CategoryTheory.Sheaf.Hypercohomology.freeAbelianSheaf.{u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k))) (SmoothSite.base (Spec (.of k)))) :=
  _root_.CategoryTheory.Sheaf.Hypercohomology.projective_freeAbelianSheaf_base k

/-- Every actual standard-Ext class with arbitrary ordinary coefficients vanishes. -/
theorem actual_ext_succ_eq_zero
    (F : Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
    (n : ℕ)
    (x : Ext.{u + 2} (_root_.CategoryTheory.Sheaf.Hypercohomology.freeAbelianSheaf.{u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k))) (SmoothSite.base (Spec (.of k))))
      F (n + 1)) : x = 0 :=
  _root_.CategoryTheory.Sheaf.LargeCohomology.H_succ_base_eq_zero k F n x

/-- Forgetting transfers gives the actual ordinary cohomology zero group at the base. -/
theorem original_transfer_sheaf_H_succ_isZero (F : SheafWithTransfers.{u + 1} k) (n : ℕ) :
    IsZero (_root_.CategoryTheory.Sheaf.LargeCohomology.H.{u + 2, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf.{u + 1} k).obj F) (n + 1)
      (SmoothSite.base (Spec (.of k)))) :=
  _root_.CategoryTheory.Sheaf.LargeCohomology.isZero_H_succ_base k _ n

#print axioms actual_ext_succ_eq_zero
#print axioms original_transfer_sheaf_H_succ_isZero

end MotivicTest.Cohomology.SheafCohomologyFieldEvaluation
