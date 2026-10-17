/-
Copyright (c) 2026 Motivic cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Motivic.Algebra.Homology.SingularComplexPresheaf
import Motivic.Cohomology.Motivic.Indexing

/-!
# Consumer tests for singular chains and weight-two indexing

These tests use arbitrary abelian-group presheaves and geometric parameters.
They check the equalizer description of degree-one cycles, that genuine
chain-two boundaries satisfy it, the actual weight-two term identifications,
and the distinction from Bloch's chain-three convention.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
open Motivic.SingularComplex

universe v u w

variable {C : Type u} [Category.{v} C]
variable (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ AddCommGrpCat.{w})

example (x : P.obj (op (Δ.obj ⦋1⦌))) :
    (obj Δ P).d 1 0 x = 0 ↔
      P.map (Δ.δ (0 : Fin 2)).op x = P.map (Δ.δ (1 : Fin 2)).op x := by
  rw [obj_d_one_zero]
  exact sub_eq_zero

example (x : P.obj (op (Δ.obj ⦋2⦌))) :
    P.map (Δ.δ (0 : Fin 2)).op ((obj Δ P).d 2 1 x) =
      P.map (Δ.δ (1 : Fin 2)).op ((obj Δ P).d 2 1 x) := by
  have h := congrArg (fun f : (obj Δ P).X 2 ⟶ (obj Δ P).X 0 => f x)
    (d_squared Δ P 0)
  change (obj Δ P).d 1 0 ((obj Δ P).d 2 1 x) = 0 at h
  rw [obj_d_one_zero] at h
  exact sub_eq_zero.mp h

example : (cochainObj Δ P 2).X 1 ≅ P.obj (op (Δ.obj ⦋1⦌)) :=
  weightTwoXOneIso Δ P

example : (cochainObj Δ P 2).X 2 ≅ P.obj (op (Δ.obj ⦋0⦌)) :=
  weightTwoXTwoIso Δ P

example : (cochainObj Δ P 2).X (-1) ≅ P.obj (op (Δ.obj ⦋3⦌)) :=
  cochainXIso Δ P 2 3

example : IsZero ((cochainObj Δ P 2).X 3) :=
  isZero_cochainObj_X Δ P 2 3 (by decide)

example : Motivic.Indexing.singularDegree 2 1 = 1 ∧
    Motivic.Indexing.blochDegree 2 1 = 3 := by
  constructor <;> rfl

variable [HasBinaryProducts C]

example (U : C) (x : P.obj (op (U ⨯ Δ.obj ⦋2⦌))) :
    (parameterObj Δ P U).d 1 0 ((parameterObj Δ P U).d 2 1 x) = 0 := by
  exact congrArg (fun f : (parameterObj Δ P U).X 2 ⟶
      (parameterObj Δ P U).X 0 => f x)
    ((parameterObj Δ P U).d_comp_d 2 1 0)

example {U V W : C} (f : U ⟶ V) (g : V ⟶ W) (n : ℕ)
    (x : P.obj (op (W ⨯ Δ.obj ⦋n⦌))) :
    (parameterMap Δ P (f ≫ g)).f n x =
      (parameterMap Δ P f).f n ((parameterMap Δ P g).f n x) := by
  rw [parameterMap_comp]
  rfl

example (U : Cᵒᵖ) (n : ℕ) :
    (((presheafObj Δ P).d (n + 2) (n + 1)) ≫
      ((presheafObj Δ P).d (n + 1) n)).app U = 0 := by
  rw [(presheafObj Δ P).d_comp_d]
  rfl
