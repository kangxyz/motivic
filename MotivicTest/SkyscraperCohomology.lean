/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.CategoryTheory.Sites.Point.SkyscraperCohomology
public import Lean.Util.CollectAxioms

/-!
# Consumers of point-skyscraper ordinary cohomology

These tests retain independent site, coefficient, and Ext universes. They
exercise exactness, the actual free source, both naturality directions,
and vanishing for arbitrary abelian coefficient groups.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe e e' w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (Φ : GrothendieckTopology.Point.{max v w} J)
  [HasSheafify J AddCommGrpCat.{max v w}]

example (S : ShortComplex AddCommGrpCat.{max v w}) (hS : S.Exact) :
    (S.map Φ.skyscraperSheafFunctor).Exact := hS.map _

example {M N : AddCommGrpCat.{max v w}} (f : M ⟶ N) [Epi f] (X : C) :
    Function.Surjective ((Φ.skyscraperSheafFunctor.map f).hom.app (op X)) := by
  have := Φ.epi_skyscraperSheaf_map_app f X
  exact (AddCommGrpCat.epi_iff_surjective _).mp inferInstance

example (X : C) :
    Projective (Φ.sheafFiber.obj (_root_.CategoryTheory.Sheaf.Hypercohomology.freeAbelianSheaf J X))
        :=
  Φ.projective_sheafFiber_freeAbelianSheaf X

variable [HasExt.{e} (Sheaf J AddCommGrpCat.{max v w})]
  [HasExt.{e'} AddCommGrpCat.{max v w}]

example (M : AddCommGrpCat.{max v w}) (n : ℕ) {X Y : C} (f : X ⟶ Y)
    (x : _root_.CategoryTheory.Sheaf.LargeCohomology.H J (Φ.skyscraperSheaf M) n Y) :
    Φ.skyscraperCohomologyComparison M n X
        ((_root_.CategoryTheory.Sheaf.LargeCohomology.presheaf J (Φ.skyscraperSheaf M) n).map f.op
            x) =
      (Ext.mk₀ (Φ.sheafFiber.map
          ((_root_.CategoryTheory.Sheaf.Hypercohomology.freeAbelianSheafFunctor J).map f))).comp
        (Φ.skyscraperCohomologyComparison M n Y x) (zero_add n) :=
  Φ.skyscraperCohomologyComparison_restriction M n f x

example {M N : AddCommGrpCat.{max v w}} (f : M ⟶ N) (n : ℕ) (X : C)
    (x : _root_.CategoryTheory.Sheaf.LargeCohomology.H J (Φ.skyscraperSheaf M) n X) :
    Φ.skyscraperCohomologyComparison N n X
        (((_root_.CategoryTheory.Sheaf.LargeCohomology.presheafFunctor J n).map
          (Φ.skyscraperSheafFunctor.map f)).app (op X) x) =
      (Φ.skyscraperCohomologyComparison M n X x).comp (Ext.mk₀ f) (add_zero n) :=
  Φ.skyscraperCohomologyComparison_coefficient f n X x

example (M : AddCommGrpCat.{max v w}) (n : ℕ) (X : C)
    (x : _root_.CategoryTheory.Sheaf.LargeCohomology.H J (Φ.skyscraperSheaf M) (n + 1) X) : x = 0 :=
  Φ.skyscraper_cohomology_eq_zero M n X x

open Lean in
run_cmd do
  for name in #[``CategoryTheory.GrothendieckTopology.Point.epi_skyscraperSheaf_map_app,
      ``CategoryTheory.GrothendieckTopology.Point.projective_sheafFiber_freeAbelianSheaf,
      ``CategoryTheory.GrothendieckTopology.Point.skyscraperCohomologyComparison,
      ``CategoryTheory.GrothendieckTopology.Point.skyscraperCohomologyComparison_restriction,
      ``CategoryTheory.GrothendieckTopology.Point.skyscraperCohomologyComparison_coefficient,
      ``CategoryTheory.GrothendieckTopology.Point.skyscraper_cohomology_eq_zero] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Point-skyscraper cohomology uses only standard Lean foundations."
