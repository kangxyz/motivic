/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.SmoothSiteBaseChange
public import Motivic.AlgebraicGeometry.SmoothSiteSimplex
public import Motivic.Algebra.Homology.SingularComplex

/-!
# Smooth-site algebraic simplex consumers

These consumers test the genuine quotient algebra in arbitrary degree, its
structure morphism, its cofaces, and its admissibility after arbitrary field
base change. They do not replace a base-changed simplex by a coefficient-changed
one without a proved pullback comparison.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Motivic.AlgebraicSimplex Motivic.SmoothSite
open scoped Simplicial

universe u

noncomputable section

namespace Motivic.MotivicTest.SmoothSiteSimplex

example (R : Type u) [CommRing R] (n : ℕ) : Algebra.Smooth R (CoordinateRing R n) :=
  inferInstance

example (R : Type u) [CommRing R] (n : ℕ) : Smooth (structureMap R n) := inferInstance

example (R : Type u) [CommRing R] (n : ℕ) : IsSeparated (structureMap R n) := inferInstance

example (R : Type u) [CommRing R] (n : ℕ) : QuasiCompact (structureMap R n) := inferInstance

example (R : Type u) [CommRing R] (n : ℕ) (i : Fin (n + 2)) :
    ((cosimplicialSmoothSite R).δ i).left =
      Spec.map (CommRingCat.ofHom (face R i)) := rfl

example (R : Type u) [CommRing R] :
    cosimplicialSmoothSite R ⋙ forget (Spec (CommRingCat.of R)) =
      cosimplicialSchemeOver R := cosimplicialSmoothSite_forget R

example {K L : Type u} [Field K] [Field L] (φ : K →+* L) (n : ℕ) :
    Smooth ((fieldBaseChange φ).obj (smoothSiteObj K n)).hom := inferInstance

example {K L : Type u} [Field K] [Field L] (φ : K →+* L) (n : ℕ) :
    ((fieldBaseChange φ).obj (smoothSiteObj K n)).left =
      CategoryTheory.Limits.pullback (structureMap K n) (Spec.map (CommRingCat.ofHom φ)) := rfl

/-- The existing all-degree singular construction now accepts actual smooth-site presheaves. -/
def smoothPresheafComplex (R : Type u) [CommRing R]
    (P : (Motivic.SmoothSite (Spec (CommRingCat.of R)))ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    ChainComplex AddCommGrpCat.{u} ℕ :=
  Motivic.SingularComplex.obj (cosimplicialSmoothSite R) P

example (R : Type u) [CommRing R]
    (P : (Motivic.SmoothSite (Spec (CommRingCat.of R)))ᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) :
    (smoothPresheafComplex R P).X n = P.obj (op (smoothSiteObj R n)) := rfl

example (R : Type u) [CommRing R]
    (P : (Motivic.SmoothSite (Spec (CommRingCat.of R)))ᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) :
    (smoothPresheafComplex R P).d (n + 2) (n + 1) ≫
      (smoothPresheafComplex R P).d (n + 1) n = 0 :=
  (smoothPresheafComplex R P).d_comp_d _ _ _

end Motivic.MotivicTest.SmoothSiteSimplex
