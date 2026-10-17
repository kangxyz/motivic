/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.TorComparison.FlatCoefficient

/-! Consumer checks for the coefficient-side flatness bridge to actual Tor. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Motivic.MotivicTest.TorComparisonFlatCoefficient

/-- The resolved argument is unrestricted when the coefficient is flat. -/
theorem flatCoefficient {R : Type u} [CommRing R]
    (M N : ModuleCat.{u} R) [Module.Flat R M] (n : ℕ) :
    IsZero (((Tor (ModuleCat R) (n + 1)).obj M).obj N) :=
  TorComparison.isZero_tor_succ_of_flat_coefficient M N n

/-- Categorical projectivity in the first argument suffices without Tor symmetry. -/
theorem projectiveCoefficient {R : Type u} [CommRing R]
    (M N : ModuleCat.{u} R) [Projective M] (n : ℕ) :
    IsZero (((Tor (ModuleCat R) (n + 1)).obj M).obj N) :=
  TorComparison.isZero_tor_succ_of_flat_coefficient M N n

/-- Arbitrarily generated free coefficients provide the intended resolution-row case. -/
theorem freeCoefficient {R : Type u} [CommRing R]
    (ι : Type u) (N : ModuleCat.{u} R) (n : ℕ) :
    IsZero (((Tor (ModuleCat R) (n + 1)).obj (ModuleCat.of R (ι →₀ R))).obj N) :=
  TorComparison.isZero_tor_succ_of_flat_coefficient _ N n

/-- No characteristic or dimension restriction is imposed on field coefficients. -/
theorem arbitraryField {k : Type u} [Field k]
    (M N : ModuleCat.{u} k) (n : ℕ) :
    IsZero (((Tor (ModuleCat k) (n + 1)).obj M).obj N) :=
  TorComparison.isZero_tor_succ_over_field M N n

/-- Exact-functor acyclicity also applies independently of any tensor structure. -/
theorem identityDerived {C : Type u} [Category C] [Abelian C]
    [HasProjectiveResolutions C] (N : C) (n : ℕ) :
    IsZero (((𝟭 C).leftDerived (n + 1)).obj N) :=
  TorComparison.isZero_leftDerived_succ_of_preservesHomology (𝟭 C) N n

end Motivic.MotivicTest.TorComparisonFlatCoefficient
