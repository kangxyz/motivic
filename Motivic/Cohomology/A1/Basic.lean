/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.Projection
public import Motivic.Transfers.Sheaf.Basic
public import Aglib.CategoryTheory.Sites.SheafCohomology.Large.Basic

/-!
# Homotopy invariance for actual projection maps

Homotopy invariance means that the literal affine-line projection induces an
isomorphism, rather than merely asking for an unspecified isomorphism of values.
Strict invariance uses the actual ordinary Ext cohomology presheaf in every
nonnegative degree. The definitions retain actual graph transfers.

The elementary results below show that every projection pullback is split by
every constant section, and identify its inverse under homotopy invariance.
They do not assert Voevodsky's strict-invariance theorem or sheafification HI.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite

universe w v u v' u'

namespace Motivic.A1
open _root_.AlgebraicGeometry.Scheme

variable (R : CommRingCat.{u})
variable {A : Type u'} [Category.{v'} A]

/-- The actual projection-induced restriction on an ordinary presheaf. -/
def projectionPullback (P : (SmoothSite (Spec R))ᵒᵖ ⥤ A)
    (X : SmoothSite (Spec R)) :
    P.obj (op X) ⟶ P.obj (op (SmoothSite.a1Cylinder R X)) :=
  P.map (SmoothSite.a1Projection R X).op

/-- Restriction along the actual constant section of the cylinder. -/
def sectionPullback (P : (SmoothSite (Spec R))ᵒᵖ ⥤ A)
    (X : SmoothSite (Spec R)) (a : R) :
    P.obj (op (SmoothSite.a1Cylinder R X)) ⟶ P.obj (op X) :=
  P.map (SmoothSite.a1Section R X a).op

@[reassoc (attr := simp)]
theorem projectionPullback_sectionPullback (P : (SmoothSite (Spec R))ᵒᵖ ⥤ A)
    (X : SmoothSite (Spec R)) (a : R) :
    projectionPullback R P X ≫ sectionPullback R P X a = 𝟙 (P.obj (op X)) := by
  simp only [projectionPullback, sectionPullback, ← P.map_comp, ← op_comp,
    SmoothSite.a1Section_projection, op_id, P.map_id]

/-- Naturality retains the actual product map in the source variable. -/
@[reassoc]
theorem projectionPullback_naturality (P : (SmoothSite (Spec R))ᵒᵖ ⥤ A)
    {X Y : SmoothSite (Spec R)} (f : X ⟶ Y) :
    P.map f.op ≫ projectionPullback R P X =
      projectionPullback R P Y ≫ P.map (SmoothSite.a1Map R f).op := by
  simp only [projectionPullback, ← P.map_comp, ← op_comp,
    SmoothSite.a1Map_projection]

/-- Naturality in the coefficient presheaf. -/
@[reassoc]
theorem projectionPullback_coefficient_naturality
    {P Q : (SmoothSite (Spec R))ᵒᵖ ⥤ A} (η : P ⟶ Q)
    (X : SmoothSite (Spec R)) :
    projectionPullback R P X ≫ η.app (op (SmoothSite.a1Cylinder R X)) =
      η.app (op X) ≫ projectionPullback R Q X :=
  η.naturality (SmoothSite.a1Projection R X).op

/-- Homotopy invariance is invertibility of the actual affine-line projection. -/
def IsInvariant (P : (SmoothSite (Spec R))ᵒᵖ ⥤ A) : Prop :=
  ∀ X : SmoothSite (Spec R), IsIso (projectionPullback R P X)

/-- Homotopy invariance gives an isomorphism with exactly the projection as its forward map. -/
def projectionIso (P : (SmoothSite (Spec R))ᵒᵖ ⥤ A) (hP : IsInvariant R P)
    (X : SmoothSite (Spec R)) :
    P.obj (op X) ≅ P.obj (op (SmoothSite.a1Cylinder R X)) := by
  letI := hP X
  exact asIso (projectionPullback R P X)

@[simp] theorem projectionIso_hom (P : (SmoothSite (Spec R))ᵒᵖ ⥤ A)
    (hP : IsInvariant R P) (X : SmoothSite (Spec R)) :
    (projectionIso R P hP X).hom = projectionPullback R P X := rfl

/-- Every constant section is the inverse once the actual projection is invertible. -/
theorem projectionIso_inv (P : (SmoothSite (Spec R))ᵒᵖ ⥤ A)
    (hP : IsInvariant R P) (X : SmoothSite (Spec R)) (a : R) :
    (projectionIso R P hP X).inv = sectionPullback R P X a := by
  apply (cancel_epi (projectionIso R P hP X).hom).mp
  exact (projectionIso R P hP X).hom_inv_id.trans
    (projectionPullback_sectionPullback R P X a).symm

/-- Homotopy-invariant coefficients give the same pullback along any two constant sections. -/
theorem sectionPullback_eq (P : (SmoothSite (Spec R))ᵒᵖ ⥤ A)
    (hP : IsInvariant R P) (X : SmoothSite (Spec R)) (a b : R) :
    sectionPullback R P X a = sectionPullback R P X b :=
  (projectionIso_inv R P hP X a).symm.trans (projectionIso_inv R P hP X b)

end Motivic.A1

namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k]

/-- A transfer presheaf is HI when its actual graph restriction is HI. -/
def IsA1Invariant (P : PresheafWithTransfers.{v} k) : Prop :=
  A1.IsInvariant (.of k) ((toPresheaf k).obj P)

/-- The affine-line pullback is the transfer along the literal graph projection. -/
@[simp] theorem a1ProjectionPullback_eq_transfer (P : PresheafWithTransfers.{v} k)
    (X : SmoothSite (Spec (.of k))) :
    A1.projectionPullback (.of k) ((toPresheaf k).obj P) X =
      transfer P ((Cor.graphFunctor k).map (SmoothSite.a1Projection (.of k) X)) := rfl

/-- On a representable transfer presheaf, the map is actual graph precomposition. -/
theorem a1ProjectionPullback_representable_apply (Y : Cor k)
    (X : SmoothSite (Spec (.of k))) (α : Cor.mk X ⟶ Y) :
    A1.projectionPullback (.of k) ((toPresheaf k).obj ((representable k).obj Y)) X α =
      (Cor.graphFunctor k).map (SmoothSite.a1Projection (.of k) X) ≫ α := rfl

/-- A genuine finite-correspondence homotopy has equal constant-endpoint actions on HI coefficients.
The cylinder correspondence may be signed and need not be the graph of a scheme map. -/
theorem transfer_homotopy_endpoints (P : PresheafWithTransfers.{v} k)
    (hP : IsA1Invariant P) (X : SmoothSite (Spec (.of k))) (Y : Cor k)
    (α : Cor.mk (SmoothSite.a1Cylinder (.of k) X) ⟶ Y) (a b : k) :
    transfer P ((Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) X a) ≫ α) =
      transfer P ((Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) X b) ≫ α) := by
  rw [transfer_comp, transfer_comp]
  have h : transfer P ((Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) X a)) =
      transfer P ((Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) X b)) :=
    A1.sectionPullback_eq (.of k) ((toPresheaf k).obj P) hP X a b
  rw [h]

end Motivic.PresheafWithTransfers

namespace Motivic.SheafWithTransfers
open _root_.AlgebraicGeometry.Scheme _root_.CategoryTheory.Sheaf

variable {k : Type u} [Field k]
variable [HasSheafify (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}]
variable [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
  AddCommGrpCat.{u + 1})]

/-- Strict HI tests every ordinary Nisnevich cohomology degree using actual projections. -/
def IsStrictA1Invariant (F : SheafWithTransfers.{u + 1} k) : Prop :=
  ∀ n : ℕ, A1.IsInvariant (.of k)
    (LargeCohomology.presheaf.{w, u + 1, u, u + 1} _ ((toSheaf k).obj F) n)

/-- Expanding strict invariance retains the ordinary cohomology projection map verbatim. -/
theorem isStrictA1Invariant_iff (F : SheafWithTransfers.{u + 1} k) :
    IsStrictA1Invariant F ↔ ∀ (n : ℕ) (X : SmoothSite (Spec (.of k))),
      IsIso ((LargeCohomology.presheaf.{w, u + 1, u, u + 1} _ ((toSheaf k).obj F) n).map
        (SmoothSite.a1Projection (.of k) X).op) := Iff.rfl

end Motivic.SheafWithTransfers
