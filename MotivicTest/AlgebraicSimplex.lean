/-
Copyright (c) 2026 Motivic Cohomology Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.AlgebraicSimplexScheme
public import Motivic.AlgebraicGeometry.AlgebraicSimplexPolynomial
public import Mathlib.Data.ZMod.Basic

/-!
# Algebraic simplex consumers

These checks exercise actual coordinate-ring evaluations, arbitrary-degree
vertex maps, degeneracy formulas, coefficient reduction modulo a composite,
and the relative scheme interface. Negative barycentric coordinates are allowed
in an algebraic simplex.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Motivic.AlgebraicSimplex
open scoped Simplicial

noncomputable section

namespace Motivic.MotivicTest.AlgebraicSimplex

/-- The integral point `(2, -1)` on the algebraic one-simplex. -/
def integerPoint : CoordinateRing ℤ 1 →+* ℤ :=
  lift (n := 1) (RingHom.id ℤ) ![2, -1] (by decide)

theorem integerPoint_product : integerPoint (coordinate ℤ 1 0 * coordinate ℤ 1 1) = -2 := by
  simp [integerPoint]

theorem vertexPullback_chosenCoordinate (R : Type*) [CommRing R] (m n : ℕ) (j : Fin (n + 1)) :
    pullback R (fun _ : Fin (m + 1) ↦ j) (coordinate R n j) = 1 := by
  simp

theorem vertexPullback_otherCoordinate (R : Type*) [CommRing R] (m n : ℕ)
    (j k : Fin (n + 1)) (h : j ≠ k) :
    pullback R (fun _ : Fin (m + 1) ↦ j) (coordinate R n k) = 0 := by
  simp [h]

theorem face_kills_coordinate_product (R : Type*) [CommRing R] :
    face R (0 : Fin 3) (coordinate R 2 0 * coordinate R 2 1) = 0 := by
  simp

theorem face_degeneracy_coordinate (R : Type*) [CommRing R] (n : ℕ) (i : Fin (n + 1)) :
    face R i.succ (degeneracy R i (coordinate R n i)) = coordinate R n i := by
  exact RingHom.congr_fun (face_comp_degeneracy_succ R i) _

theorem mod_six_vanishes (n : ℕ) :
    mapCoefficients (Int.castRingHom (ZMod 6)) n (6 : CoordinateRing ℤ n) = 0 := by
  calc
    _ = constant (ZMod 6) n (6 : ZMod 6) := by simp only [map_ofNat]
    _ = 0 := by
      have h : (6 : ZMod 6) = 0 := by decide
      rw [h, map_zero]

theorem relative_coface_underlying_map (R : Type*) [CommRing R] (n : ℕ) (i : Fin (n + 2)) :
    ((cosimplicialSchemeOver R).δ i).left =
      Spec.map (CommRingCat.ofHom (face R i)) := rfl

theorem polynomialChart_coordinate_product (R : Type*) [CommRing R] (n : ℕ) (i j : Fin n) :
    polynomialEquiv R n (coordinate R n i.castSucc * coordinate R n j.castSucc) =
      MvPolynomial.X i * MvPolynomial.X j := by
  simp

end Motivic.MotivicTest.AlgebraicSimplex
