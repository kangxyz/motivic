/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.StrictInvariance.DegreeZero

/-!
# Direct standard-Ext consumers of the strict-invariance base case

These consumers use the standard Ext instance over an arbitrary field and the
original transfer-sheaf coefficient universe. Projection and zero-section
actions are written directly as composition with the corresponding actual
free-sheaf Ext classes, including the nontrivial inverse identity on the cylinder.
-/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry Opposite Motivic

universe u

namespace MotivicTest.Cohomology.A1DegreeZero

variable {k : Type u} [Field k]

local instance : HasExt.{u + 2}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}) :=
  HasExt.standard _

/-- The forward map on the actual standard Ext group is bijective for HI coefficients. -/
theorem actual_ext_projection_bijective (F : SheafWithTransfers.{u + 1} k)
    (hF : F.obj.IsA1Invariant) (X : SmoothSite (Spec (.of k))) :
    Function.Bijective (fun x : Ext
      (_root_.CategoryTheory.Sheaf.Hypercohomology.freeAbelianSheaf.{u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) X)
      ((SheafWithTransfers.toSheaf k).obj F) 0 =>
        (Ext.mk₀ ((_root_.CategoryTheory.Sheaf.Hypercohomology.freeAbelianSheafFunctor.{u + 1, u, u
          + 1}
          (SmoothSite.nisnevichTopology (Spec (.of k)))).map
            (SmoothSite.a1Projection (.of k) X))).comp x (zero_add 0)) :=
  (ConcreteCategory.isIso_iff_bijective _).mp
    (SheafWithTransfers.degreeZero_isInvariant F hF X)

/-- On the cylinder, zero-section restriction followed by projection is the identity
on the actual Ext classes, not only on an abstractly isomorphic group. -/
theorem actual_ext_zero_section_inverse (F : SheafWithTransfers.{u + 1} k)
    (hF : F.obj.IsA1Invariant) (X : SmoothSite (Spec (.of k)))
    (x : Ext (_root_.CategoryTheory.Sheaf.Hypercohomology.freeAbelianSheaf.{u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k))) (SmoothSite.a1Cylinder (.of k) X))
      ((SheafWithTransfers.toSheaf k).obj F) 0) :
    (Ext.mk₀ ((_root_.CategoryTheory.Sheaf.Hypercohomology.freeAbelianSheafFunctor.{u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k)))).map
          (SmoothSite.a1Projection (.of k) X))).comp
      ((Ext.mk₀ ((_root_.CategoryTheory.Sheaf.Hypercohomology.freeAbelianSheafFunctor.{u + 1, u, u +
        1}
          (SmoothSite.nisnevichTopology (Spec (.of k)))).map
            (SmoothSite.a1Section (.of k) X 0))).comp x (zero_add 0)) (zero_add 0) = x := by
  have h := ConcreteCategory.congr_hom
    (SheafWithTransfers.degreeZeroProjectionIso F hF X).inv_hom_id x
  change (SheafWithTransfers.degreeZeroProjectionIso F hF X).hom
    ((SheafWithTransfers.degreeZeroProjectionIso F hF X).inv x) = x at h
  rw [SheafWithTransfers.degreeZeroProjectionIso_hom,
    SheafWithTransfers.degreeZeroProjectionIso_inv] at h
  exact h

/-- The degree-zero equivalence tests the original sections projection at every object. -/
theorem actual_projection_iff (F : SheafWithTransfers.{u + 1} k)
    (X : SmoothSite (Spec (.of k))) :
    IsIso ((_root_.CategoryTheory.Sheaf.LargeCohomology.presheaf.{u + 2, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k))) ((SheafWithTransfers.toSheaf k).obj F)
        0).map (SmoothSite.a1Projection (.of k) X).op) ↔
      IsIso (PresheafWithTransfers.transfer F.obj
        ((Cor.graphFunctor k).map (SmoothSite.a1Projection (.of k) X))) :=
  SheafWithTransfers.degreeZero_isIso_projection_iff F X

/-- A strict-invariance assumption entails the actual sections-level condition. -/
theorem strict_implies_original_HI (F : SheafWithTransfers.{u + 1} k)
    (hF : F.IsStrictA1Invariant) : F.obj.IsA1Invariant :=
  hF.isA1Invariant

/-- The concrete zero-section inverse is natural under every actual smooth-site map. -/
theorem inverse_natural_in_source (F : SheafWithTransfers.{u + 1} k)
    (hF : F.obj.IsA1Invariant) {X Y : SmoothSite (Spec (.of k))} (f : X ⟶ Y) :
    (_root_.CategoryTheory.Sheaf.LargeCohomology.presheaf.{u + 2, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k))) ((SheafWithTransfers.toSheaf k).obj F)
        0).map (SmoothSite.a1Map (.of k) f).op ≫
        (SheafWithTransfers.degreeZeroProjectionIso F hF X).inv =
      (SheafWithTransfers.degreeZeroProjectionIso F hF Y).inv ≫
        (_root_.CategoryTheory.Sheaf.LargeCohomology.presheaf.{u + 2, u + 1}
          (SmoothSite.nisnevichTopology (Spec (.of k)))
          ((SheafWithTransfers.toSheaf k).obj F) 0).map f.op :=
  SheafWithTransfers.degreeZeroProjectionIso_inv_naturality F hF f

/-- Coefficient changes commute with the same actual zero-section inverse. -/
theorem inverse_natural_in_coefficients {F G : SheafWithTransfers.{u + 1} k}
    (η : F ⟶ G) (hF : F.obj.IsA1Invariant) (hG : G.obj.IsA1Invariant)
    (X : SmoothSite (Spec (.of k))) :
    (SheafWithTransfers.degreeZeroProjectionIso F hF X).inv ≫
        ((_root_.CategoryTheory.Sheaf.LargeCohomology.presheafFunctor.{u + 2, u + 1}
          (SmoothSite.nisnevichTopology (Spec (.of k))) 0).map
            ((SheafWithTransfers.toSheaf k).map η)).app (op X) =
      ((_root_.CategoryTheory.Sheaf.LargeCohomology.presheafFunctor.{u + 2, u + 1}
          (SmoothSite.nisnevichTopology (Spec (.of k))) 0).map
            ((SheafWithTransfers.toSheaf k).map η)).app
              (op (SmoothSite.a1Cylinder (.of k) X)) ≫
        (SheafWithTransfers.degreeZeroProjectionIso G hG X).inv :=
  SheafWithTransfers.degreeZeroProjectionIso_inv_coefficient_naturality η hF hG X

end MotivicTest.Cohomology.A1DegreeZero
