/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.SmoothSiteNisnevichPointRefinement
public import Lean.Util.CollectAxioms

/-! # Actual composed-neighborhood and original cocone consumers -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Motivic.SmoothSite

universe u v

variable {S : Scheme.{u}} [IsAffine S] {X : Motivic.SmoothSite S} {x : X.left}
  (N : NisnevichNeighborhood X x)

example (M : NisnevichNeighborhood ((nisnevichNeighborhoodFunctor X x).obj N) N.center) :
    ∃ (P : NisnevichNeighborhood X x) (q : P ⟶ N)
      (t : (nisnevichNeighborhoodFunctor X x).obj P ⟶
        (nisnevichNeighborhoodFunctor ((nisnevichNeighborhoodFunctor X x).obj N) N.center).obj M),
      IsIso t.left ∧ t ≫ M.toBase = (nisnevichNeighborhoodFunctor X x).map q :=
  N.exists_refinement_of_center_neighborhood M

variable (F : (Motivic.SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v})
  (s t : F.obj (op ((nisnevichNeighborhoodFunctor X x).obj N)))

example (hst : sectionToNisnevichPoint F ((nisnevichNeighborhoodFunctor X x).obj N) N.center s =
    sectionToNisnevichPoint F ((nisnevichNeighborhoodFunctor X x).obj N) N.center t) :
    (nisnevichPointFiberCocone X x F).ι.app (op N) s =
      (nisnevichPointFiberCocone X x F).ι.app (op N) t :=
  nisnevichPointFiberCocone_eq_of_center_germ_eq F N s t hst

open Lean in
run_cmd do
  for name in #[``AlgebraicGeometry.Scheme.Hom.exists_residueField_factorization,
      ``Motivic.SmoothSite.NisnevichNeighborhood.exists_refinement_of_center_neighborhood,
      ``Motivic.SmoothSite.nisnevichPointFiberCocone_eq_zero_of_center_germ_eq_zero,
      ``Motivic.SmoothSite.nisnevichPointFiberCocone_eq_of_center_germ_eq] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual center refinements preserve the original point-fiber cocone at arbitrary points."
