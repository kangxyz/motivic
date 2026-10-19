/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Flat coefficients in the actual one-sided Tor functor

Mathlib defines Tor by resolving its second argument. Exactness of tensoring
with a flat first argument therefore proves positive-degree vanishing directly,
without any symmetry or balanced-Tor theorem. This supplies row acyclicity for
future double-resolution comparisons. It does not prove a change-of-ambient
comparison, and does not assert flatness of correspondence support modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u

namespace ModuleCat.TorComparison

/-- An exact additive functor has zero positive left derived functors. -/
theorem isZero_leftDerived_succ_of_preservesHomology
    {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [HasProjectiveResolutions C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [F.PreservesHomology] (N : C) (n : ℕ) :
    IsZero ((F.leftDerived (n + 1)).obj N) := by
  let P := projectiveResolution N
  refine IsZero.of_iso ?_ (P.isoLeftDerivedObj F (n + 1))
  erw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact (P.complex_exactAt_succ n).map F

/-- A flat first argument kills positive actual Tor, even when the second
argument is not flat or projective. No interchange of arguments is used. -/
theorem isZero_tor_succ_of_flat_coefficient
    {R : Type u} [CommRing R] (M N : ModuleCat.{u} R) [Module.Flat R M] (n : ℕ) :
    IsZero (((Tor (ModuleCat R) (n + 1)).obj M).obj N) :=
  isZero_leftDerived_succ_of_preservesHomology
    ((tensoringLeft (ModuleCat R)).obj M) N n

/-- All positive categorical Tor groups over an arbitrary field vanish. -/
theorem isZero_tor_succ_over_field
    {k : Type u} [Field k] (M N : ModuleCat.{u} k) (n : ℕ) :
    IsZero (((Tor (ModuleCat k) (n + 1)).obj M).obj N) :=
  isZero_tor_succ_of_flat_coefficient M N n

end ModuleCat.TorComparison
