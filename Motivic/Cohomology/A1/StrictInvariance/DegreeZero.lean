/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.Basic
public import Motivic.Aglib.CategoryTheory.Sites.SheafCohomology.Large.DegreeZero

/-!
# The degree-zero base case of strict affine-line invariance

The canonical comparison of actual free-sheaf Ext in degree zero with sections
intertwines the literal projection maps. Consequently ordinary `H⁰` is homotopy
invariant exactly when the original sheaf with transfers is homotopy invariant.
The inverse is restriction along the actual zero section, naturally in both
the smooth object and the coefficient sheaf. No positive-degree invariance is
asserted, and the original coefficient universe is retained.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe w t v u

namespace Motivic.SheafCohomology
open _root_.CategoryTheory.Sheaf.LargeCohomology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v t}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{max v t})]

/-- Actual degree-zero restriction is invertible exactly when restriction of sections is.
The comparison is an additive equivalence even when the two group universes differ. -/
theorem zero_isIso_restriction_iff (F : Sheaf J AddCommGrpCat.{max v t})
    {X Y : C} (f : X ⟶ Y) :
    IsIso ((presheaf J F 0).map f.op) ↔ IsIso (F.obj.map f.op) := by
  rw [ConcreteCategory.isIso_iff_bijective, ConcreteCategory.isIso_iff_bijective]
  have h : ⇑((presheaf J F 0).map f.op) =
      (zeroSections J F X).symm ∘ F.obj.map f.op ∘ zeroSections J F Y := by
    funext x
    apply (zeroSections J F X).injective
    exact (zeroSections_restriction J F f x).trans
      ((zeroSections J F X).apply_symm_apply _).symm
  rw [h]
  exact (Equiv.comp_bijective _ (zeroSections J F X).symm.toEquiv).trans
    ((zeroSections J F Y).toEquiv.bijective_comp _)

end Motivic.SheafCohomology

namespace Motivic.SheafWithTransfers
open _root_.AlgebraicGeometry.Scheme _root_.CategoryTheory.Sheaf

variable {k : Type u} [Field k]
variable [HasSheafify (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}]
variable [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
  AddCommGrpCat.{u + 1})]

/-- The actual ordinary `H⁰` projection is invertible exactly when the original
graph-restricted sections projection is invertible. -/
theorem degreeZero_isIso_projection_iff (F : SheafWithTransfers.{u + 1} k)
    (X : SmoothSite (Spec (.of k))) :
    IsIso (A1.projectionPullback (.of k)
      (LargeCohomology.presheaf.{w, u + 1, u, u + 1} _ ((toSheaf k).obj F) 0) X) ↔
    IsIso (A1.projectionPullback (.of k)
      ((PresheafWithTransfers.toPresheaf k).obj F.obj) X) :=
  SheafCohomology.zero_isIso_restriction_iff _ _ (SmoothSite.a1Projection (.of k) X)

/-- Homotopy invariance of the original transfer sheaf is exactly degree-zero
homotopy invariance for its actual ordinary cohomology. -/
theorem degreeZero_isInvariant_iff (F : SheafWithTransfers.{u + 1} k) :
    A1.IsInvariant (.of k)
      (LargeCohomology.presheaf.{w, u + 1, u, u + 1} _ ((toSheaf k).obj F) 0) ↔
      F.obj.IsA1Invariant :=
  forall_congr' (degreeZero_isIso_projection_iff F)

/-- The unconditional degree-zero base case: HI coefficients give HI ordinary `H⁰`. -/
theorem degreeZero_isInvariant (F : SheafWithTransfers.{u + 1} k)
    (hF : F.obj.IsA1Invariant) :
    A1.IsInvariant (.of k)
      (LargeCohomology.presheaf.{w, u + 1, u, u + 1} _ ((toSheaf k).obj F) 0) :=
  (degreeZero_isInvariant_iff F).mpr hF

/-- Strict affine-line invariance includes homotopy invariance of the original sections. -/
theorem IsStrictA1Invariant.isA1Invariant {F : SheafWithTransfers.{u + 1} k}
    (hF : F.IsStrictA1Invariant) : F.obj.IsA1Invariant :=
  (degreeZero_isInvariant_iff F).mp (hF 0)

/-- The actual degree-zero projection isomorphism for HI coefficients. -/
def degreeZeroProjectionIso (F : SheafWithTransfers.{u + 1} k)
    (hF : F.obj.IsA1Invariant) (X : SmoothSite (Spec (.of k))) :
    LargeCohomology.H.{w, u + 1, u, u + 1} _ ((toSheaf k).obj F) 0 X ≅
      LargeCohomology.H.{w, u + 1, u, u + 1} _ ((toSheaf k).obj F) 0
        (SmoothSite.a1Cylinder (.of k) X) :=
  A1.projectionIso (.of k) _ (degreeZero_isInvariant F hF) X

@[simp]
theorem degreeZeroProjectionIso_hom (F : SheafWithTransfers.{u + 1} k)
    (hF : F.obj.IsA1Invariant) (X : SmoothSite (Spec (.of k))) :
    (degreeZeroProjectionIso F hF X).hom =
      (LargeCohomology.presheaf.{w, u + 1, u, u + 1} _ ((toSheaf k).obj F) 0).map
        (SmoothSite.a1Projection (.of k) X).op := rfl

/-- The inverse is restriction along the literal zero section. -/
theorem degreeZeroProjectionIso_inv (F : SheafWithTransfers.{u + 1} k)
    (hF : F.obj.IsA1Invariant) (X : SmoothSite (Spec (.of k))) :
    (degreeZeroProjectionIso F hF X).inv =
      (LargeCohomology.presheaf.{w, u + 1, u, u + 1} _ ((toSheaf k).obj F) 0).map
        (SmoothSite.a1Section (.of k) X 0).op :=
  A1.projectionIso_inv (.of k) _ (degreeZero_isInvariant F hF) X 0

/-- The actual zero-section inverse is natural in every smooth-site morphism. -/
@[reassoc]
theorem degreeZeroProjectionIso_inv_naturality (F : SheafWithTransfers.{u + 1} k)
    (hF : F.obj.IsA1Invariant) {X Y : SmoothSite (Spec (.of k))} (f : X ⟶ Y) :
    (LargeCohomology.presheaf.{w, u + 1, u, u + 1} _ ((toSheaf k).obj F) 0).map
        (SmoothSite.a1Map (.of k) f).op ≫ (degreeZeroProjectionIso F hF X).inv =
      (degreeZeroProjectionIso F hF Y).inv ≫
        (LargeCohomology.presheaf.{w, u + 1, u, u + 1} _ ((toSheaf k).obj F) 0).map f.op := by
  simp only [degreeZeroProjectionIso_inv, ← Functor.map_comp, ← op_comp,
    SmoothSite.a1Section_naturality]

/-- The actual zero-section inverse is natural in coefficient morphisms. -/
@[reassoc]
theorem degreeZeroProjectionIso_inv_coefficient_naturality
    {F G : SheafWithTransfers.{u + 1} k} (η : F ⟶ G)
    (hF : F.obj.IsA1Invariant) (hG : G.obj.IsA1Invariant)
    (X : SmoothSite (Spec (.of k))) :
    (degreeZeroProjectionIso F hF X).inv ≫
        ((LargeCohomology.presheafFunctor.{w, u + 1, u, u + 1} _ 0).map
          ((toSheaf k).map η)).app (op X) =
      ((LargeCohomology.presheafFunctor.{w, u + 1, u, u + 1} _ 0).map
          ((toSheaf k).map η)).app (op (SmoothSite.a1Cylinder (.of k) X)) ≫
        (degreeZeroProjectionIso G hG X).inv := by
  rw [degreeZeroProjectionIso_inv, degreeZeroProjectionIso_inv]
  exact ((LargeCohomology.presheafFunctor.{w, u + 1, u, u + 1} _ 0).map
    ((toSheaf k).map η)).naturality (SmoothSite.a1Section (.of k) X 0).op

end Motivic.SheafWithTransfers
