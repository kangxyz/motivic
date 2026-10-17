/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.Basic
public import Motivic.Cohomology.SheafCohomologyNaturality

/-!
# Consumers of the actual affine-line invariance interface

The tests retain literal polynomial spectra, graph precomposition, actual
ordinary-cohomology restrictions and both functorial variables. They impose
no perfectness, infinitude or characteristic restriction on their field.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite Motivic

universe w v u

variable {k : Type u} [Field k]

example : (SmoothSite.affineLine (.of k)).left = Spec (.of (Polynomial k)) := rfl

example (X : SmoothSite (Spec (.of k))) :
    (SmoothSite.a1Projection (.of k) X).left =
      Limits.pullback.fst X.hom
        (Scheme.PolynomialLaurent.polynomialProjection (.of k)) := rfl

example (X : SmoothSite (Spec (.of k))) :
    SmoothSite.a1Section (.of k) X 0 ≫ SmoothSite.a1Projection (.of k) X = 𝟙 X :=
  SmoothSite.a1Section_projection (.of k) X 0

example (P : PresheafWithTransfers.{v} k) (X : SmoothSite (Spec (.of k))) :
    A1.projectionPullback (.of k) ((PresheafWithTransfers.toPresheaf k).obj P) X ≫
      A1.sectionPullback (.of k) ((PresheafWithTransfers.toPresheaf k).obj P) X 0 = 𝟙 _ :=
  A1.projectionPullback_sectionPullback (.of k) _ X 0

example (Y : Cor k) (X : SmoothSite (Spec (.of k))) (α : Cor.mk X ⟶ Y) :
    A1.projectionPullback (.of k)
      ((PresheafWithTransfers.toPresheaf k).obj ((PresheafWithTransfers.representable k).obj Y))
      X α = (Cor.graphFunctor k).map (SmoothSite.a1Projection (.of k) X) ≫ α :=
  PresheafWithTransfers.a1ProjectionPullback_representable_apply Y X α

example (P : PresheafWithTransfers.{v} k) (hP : P.IsA1Invariant)
    (X : SmoothSite (Spec (.of k))) :
    A1.sectionPullback (.of k) ((PresheafWithTransfers.toPresheaf k).obj P) X 0 =
      A1.sectionPullback (.of k) ((PresheafWithTransfers.toPresheaf k).obj P) X 1 :=
  A1.sectionPullback_eq (.of k) _ hP X 0 1

section Cohomology

variable [HasSheafify (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}]
variable [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
  AddCommGrpCat.{u + 1})]

example (F : SheafWithTransfers.{u + 1} k) (hF : F.IsStrictA1Invariant)
    (n : ℕ) (X : SmoothSite (Spec (.of k))) :
    IsIso ((SheafCohomology.presheaf.{w, u + 1, u, u + 1}
      _ ((SheafWithTransfers.toSheaf k).obj F) n).map
      (SmoothSite.a1Projection (.of k) X).op) := hF n X

example (F : SheafWithTransfers.{u + 1} k) (n : ℕ)
    {X Y : SmoothSite (Spec (.of k))} (f : X ⟶ Y) :
    (SheafCohomology.presheaf.{w, u + 1, u, u + 1}
      _ ((SheafWithTransfers.toSheaf k).obj F) n).map f.op ≫
      A1.projectionPullback (.of k)
        (SheafCohomology.presheaf.{w, u + 1, u, u + 1}
      _ ((SheafWithTransfers.toSheaf k).obj F) n) X =
    A1.projectionPullback (.of k)
        (SheafCohomology.presheaf.{w, u + 1, u, u + 1}
      _ ((SheafWithTransfers.toSheaf k).obj F) n) Y ≫
      (SheafCohomology.presheaf.{w, u + 1, u, u + 1}
      _ ((SheafWithTransfers.toSheaf k).obj F) n).map
        (SmoothSite.a1Map (.of k) f).op :=
  A1.projectionPullback_naturality (.of k) _ f

example {F G : SheafWithTransfers.{u + 1} k} (η : F ⟶ G) (n : ℕ)
    (X : SmoothSite (Spec (.of k))) :
    A1.projectionPullback (.of k)
        (SheafCohomology.presheaf.{w, u + 1, u, u + 1}
      _ ((SheafWithTransfers.toSheaf k).obj F) n) X ≫
      ((SheafCohomology.presheafFunctor.{w, u + 1, u, u + 1} _ n).map
        ((SheafWithTransfers.toSheaf k).map η)).app (op (SmoothSite.a1Cylinder (.of k) X)) =
    ((SheafCohomology.presheafFunctor.{w, u + 1, u, u + 1} _ n).map
        ((SheafWithTransfers.toSheaf k).map η)).app (op X) ≫
      A1.projectionPullback (.of k)
        (SheafCohomology.presheaf.{w, u + 1, u, u + 1}
      _ ((SheafWithTransfers.toSheaf k).obj G) n) X :=
  A1.projectionPullback_coefficient_naturality (.of k) _ X

end Cohomology

section OrdinaryComparison

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

example (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) {X Y : C} (f : X ⟶ Y) :
    (SheafCohomology.presheaf J F n).map f.op ≫
        ((SheafCohomology.ordinaryComparison J n).hom.app F).app (op X) =
      ((SheafCohomology.ordinaryComparison J n).hom.app F).app (op Y) ≫
        (F.cohomologyPresheaf n).map f.op :=
  ((SheafCohomology.ordinaryComparison J n).hom.app F).naturality f.op

end OrdinaryComparison

section DerivedProjection

variable [HasSheafify (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}]
variable [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
  AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
  AddCommGrpCat.{u + 1})]

example (F : SheafWithTransfers.{u + 1} k) (n : ℕ)
    (X : SmoothSite (Spec (.of k)))
    (x : Hypercohomology.H _
      ((CochainComplex.singleFunctor _ 0).obj ((SheafWithTransfers.toSheaf k).obj F))
      (n : ℤ) X) :
    SheafCohomology.singleComparison.{w, w, u + 1, u, u + 1}
        _ ((SheafWithTransfers.toSheaf k).obj F) n
        (SmoothSite.a1Cylinder (.of k) X)
        (Hypercohomology.restriction _
          ((CochainComplex.singleFunctor _ 0).obj ((SheafWithTransfers.toSheaf k).obj F))
          (n : ℤ) (SmoothSite.a1Projection (.of k) X) x) =
      A1.projectionPullback (.of k)
        (SheafCohomology.presheaf.{w, u + 1, u, u + 1}
      _ ((SheafWithTransfers.toSheaf k).obj F) n) X
        (SheafCohomology.singleComparison.{w, w, u + 1, u, u + 1}
        _ ((SheafWithTransfers.toSheaf k).obj F) n X x) :=
  SheafCohomology.singleComparison_restriction.{w, w, u + 1, u, u + 1}
    _ _ n (SmoothSite.a1Projection (.of k) X) x

end DerivedProjection
