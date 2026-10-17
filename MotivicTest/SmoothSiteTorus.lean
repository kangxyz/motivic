/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.SmoothSiteTorus
public import Mathlib.Algebra.Ring.PUnit
public import Mathlib.Data.ZMod.Basic
public import Lean.Util.CollectAxioms

/-! # Actual smooth torus powers and identity-coordinate consumers -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open AlgebraicGeometry.Scheme.PolynomialLaurent Motivic.SmoothSite

universe u

namespace MotivicTest.SmoothSiteTorus

variable (R : CommRingCat.{u})

example : (torus R).left = Spec (.of (LaurentPolynomial R)) := rfl

example : (torus R).hom = laurentProjection R := rfl

example : (torusPower R 0).left = Spec R := rfl

example : (torusPower R 0).hom = 𝟙 (Spec R) := rfl

example (q : ℕ) : (torusPower R (q + 1)).left =
    pullback (laurentProjection R) (torusPower R q).hom := rfl

example (q : ℕ) : Smooth (torusPower R q).hom := inferInstance

example (q : ℕ) : IsSeparated (torusPower R q).hom := inferInstance

example (q : ℕ) : LocallyOfFiniteType (torusPower R q).hom ∧
    QuasiCompact (torusPower R q).hom := finiteType _

example (q : ℕ) (i : Fin (q + 1)) :
    torusInsertOne R q i ≫ torusCoordinate R (q + 1) i =
      torusPowerToBase R q ≫ torusOne R :=
  torusInsertOne_coordinate_self R q i

example (q : ℕ) (i : Fin (q + 1)) (j : Fin q) :
    torusInsertOne R q i ≫ torusCoordinate R (q + 1) (i.succAbove j) =
      torusCoordinate R q j :=
  torusInsertOne_coordinate_succAbove R q i j

example (q : ℕ) (i : Fin (q + 1)) :
    (torusInsertOne R q i).left ≫ (torusCoordinate R (q + 1) i).left =
      (torusPower R q).hom ≫ laurentOneSection R :=
  torusInsertOne_left_coordinate_self R q i

example (q : ℕ) (i : Fin (q + 1)) :
    torusInsertOne R q i ≫ torusDeleteCoordinate R q i = 𝟙 (torusPower R q) :=
  torusInsertOne_deleteCoordinate R q i

example (q : ℕ) (i : Fin (q + 1)) :
    IsClosedImmersion (torusInsertOne R q i).left := inferInstance

example : torusInsertOne R 0 0 ≫ (torusPowerOneIso R).hom = torusOne R :=
  torusInsertOne_zero_powerOneIso R

example (k : Type u) [Field k] (q : ℕ) : SmoothSite (Spec (.of k)) :=
  torusPower (.of k) q

example (q : ℕ) : Smooth (torusPower (.of PUnit) q).hom := inferInstance

example (q : ℕ) (i : Fin (q + 1)) :
    IsClosedImmersion (torusInsertOne (.of (ZMod 4)) q i).left := inferInstance

open Lean in
run_cmd do
  for name in #[``torus, ``torusOne, ``torusPower, ``torusCoordinate, ``torusPowerLift,
      ``torusPowerLift_coordinate, ``torusPower_hom_ext, ``torusInsertOne,
      ``torusInsertOne_coordinate_self, ``torusInsertOne_coordinate_succAbove,
      ``torusInsertOne_left_coordinate_self, ``torusInsertOne_left_coordinate_succAbove,
      ``torusInsertOne_deleteCoordinate, ``instIsClosedImmersionTorusInsertOne,
      ``torusPowerOneIso, ``torusInsertOne_zero_powerOneIso] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"

end MotivicTest.SmoothSiteTorus
