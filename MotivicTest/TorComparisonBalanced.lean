/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.Balanced
public import Mathlib.Data.ZMod.Basic

/-! # Consumers of actual all-degree balanced Tor -/

@[expose] public section

noncomputable section

open CategoryTheory
open HomologicalComplex
open _root_.ComplexShape
open _root_.HomologicalComplex
open _root_.HomologicalComplex₂
open _root_.ModuleCat.TorComparison

universe u

namespace MotivicTest.TorComparisonBalanced

/-- The nonnegative total swap uses the genuine Koszul sign. -/
theorem actualSign (p q : ℕ) :
    ComplexShape.σ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) p q = (-1 : ℤˣ) ^ (p * q) := rfl

/-- Quotient coefficients need not be flat or regular for Tor balance. -/
def arbitraryQuotients (R : Type u) [CommRing R] (I J : Ideal R) (n : ℕ) :
    ((Tor (ModuleCat R) n).obj (ModuleCat.of R (R ⧸ I))).obj
        (ModuleCat.of R (R ⧸ J)) ≅
      ((Tor (ModuleCat R) n).obj (ModuleCat.of R (R ⧸ J))).obj
        (ModuleCat.of R (R ⧸ I)) :=
  torBalanceIso _ _ n

/-- The actual double-resolution comparison permits a non-domain product ring. -/
def productRing (R S : Type u) [CommRing R] [CommRing S]
    (M N : ModuleCat.{u} (R × S))
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N) (n : ℕ) :
    ((Tor (ModuleCat (R × S)) n).obj M).obj N ≅
      ((Tor (ModuleCat (R × S)) n).obj N).obj M :=
  torBalanceIsoOfResolutions P Q n

/-- Nilpotents in the base ring are admitted by the all-degree theorem. -/
def nonreducedBase (M N : ModuleCat (ZMod 4)) (n : ℕ) :
    ((Tor (ModuleCat (ZMod 4)) n).obj M).obj N ≅
      ((Tor (ModuleCat (ZMod 4)) n).obj N).obj M :=
  torBalanceIso M N n

/-- The comparison is a genuine inverse pair on actual Tor modules. -/
theorem hom_inv (R : Type u) [CommRing R] (M N : ModuleCat.{u} R) (n : ℕ) :
    (torBalanceIso M N n).hom ≫ (torBalanceIso M N n).inv = 𝟙 _ :=
  (torBalanceIso M N n).hom_inv_id

end MotivicTest.TorComparisonBalanced
