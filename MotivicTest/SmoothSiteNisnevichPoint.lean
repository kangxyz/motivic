/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Point.Basic
public import Motivic.Aglib.CategoryTheory.Sites.Point.SkyscraperCohomology
public import Lean.Util.CollectAxioms

/-!
# Consumers of actual smooth Nisnevich points

The tests retain arbitrary affine bases, arbitrary fields, and the existing
coefficient universe. They check pointedness, actual common-refinement
and equalization maps, restriction/coefficients in the fiber colimit, and the
single-point ordinary-cohomology consequence.
-/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open  _root_.AlgebraicGeometry.Scheme.SmoothSite

universe u v w e e'

section AffineBase

variable {S : Scheme.{u}} [IsAffine S] (X : SmoothSite S) (x : X.left)

example : IsCofiltered (NisnevichNeighborhood X x) := inferInstance

example : InitiallySmall.{u + 1} (NisnevichNeighborhood X x) := inferInstance

example (N : NisnevichNeighborhood X x) :
    N.obj.val.left ≫ N.obj.obj.hom = X.left.fromSpecResidueField x := Over.w N.obj.val

example (N M : NisnevichNeighborhood X x) :
    ∃ W : NisnevichNeighborhood X x, Nonempty (W ⟶ N) ∧ Nonempty (W ⟶ M) :=
  ⟨IsCofiltered.min N M, ⟨IsCofiltered.minToLeft N M⟩, ⟨IsCofiltered.minToRight N M⟩⟩

example {N M : NisnevichNeighborhood X x} (f g : N ⟶ M) :
    ∃ (W : NisnevichNeighborhood X x) (q : W ⟶ N),
      ((nisnevichNeighborhoodFunctor X x).map q).left ≫
          ((nisnevichNeighborhoodFunctor X x).map f).left =
        ((nisnevichNeighborhoodFunctor X x).map q).left ≫
          ((nisnevichNeighborhoodFunctor X x).map g).left := by
  refine ⟨IsCofiltered.eq f g, IsCofiltered.eqHom f g, ?_⟩
  exact congrArg (fun h ↦ ((nisnevichNeighborhoodFunctor X x).map h).left)
    (IsCofiltered.eq_condition f g)

variable {A : Type v} [Category.{w} A] [HasColimitsOfSize.{u + 1, u + 1} A]

example (F : (SmoothSite S)ᵒᵖ ⥤ A) :
    IsColimit (nisnevichPointFiberCocone X x F) := isColimitNisnevichPointFiberCocone X x F

example (F : (SmoothSite S)ᵒᵖ ⥤ A) {N M : NisnevichNeighborhood X x} (f : N ⟶ M) :
    F.map ((nisnevichNeighborhoodFunctor X x).map f).op ≫
        (nisnevichPointFiberCocone X x F).ι.app (op N) =
      (nisnevichPointFiberCocone X x F).ι.app (op M) :=
  (nisnevichPointFiberCocone X x F).w f.op

example {F G : (SmoothSite S)ᵒᵖ ⥤ A} (φ : F ⟶ G) (N : NisnevichNeighborhood X x) :
    (nisnevichPointFiberCocone X x F).ι.app (op N) ≫
        (nisnevichPoint X x).presheafFiber.map φ =
      φ.app (op ((nisnevichNeighborhoodFunctor X x).obj N)) ≫
        (nisnevichPointFiberCocone X x G).ι.app (op N) :=
  nisnevichPointFiberCocone_naturality X x φ N

end AffineBase

section ArbitraryField

variable (k : Type u) [Field k] (X : SmoothSite (Spec (.of k))) (x : X.left)

example : (nisnevichTopology (Spec (.of k))).Point.{u + 1} := nisnevichPoint X x

variable [HasExt.{e} (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasExt.{e'} AddCommGrpCat.{u + 1}]

example (M : AddCommGrpCat.{u + 1}) (n : ℕ) (Y : SmoothSite (Spec (.of k)))
    (a : _root_.CategoryTheory.Sheaf.LargeCohomology.H.{e, u + 1, u, u + 1} (nisnevichTopology (Spec
        (.of k)))
      ((nisnevichPoint X x).skyscraperSheaf M) (n + 1) Y) : a = 0 :=
  GrothendieckTopology.Point.skyscraper_cohomology_eq_zero.{e, e', u + 1, u, u + 1}
    (nisnevichPoint X x) M n Y a

end ArbitraryField

open Lean in
run_cmd do
  for name in #[``_root_.AlgebraicGeometry.Scheme.SmoothSite.exists_smoothNeighborhood_refinement,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.nisnevichNeighborhoodFunctor,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.nisnevichNeighborhood_cover_lifting,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.nisnevichPoint,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.isColimitNisnevichPointFiberCocone,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.nisnevichPointFiberCocone_naturality] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Smooth Nisnevich points use only standard Lean foundations."
