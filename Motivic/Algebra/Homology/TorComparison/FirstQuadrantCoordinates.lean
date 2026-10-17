/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Coordinates and finite filtrations on actual first-quadrant totals

The projections and filtration endomorphisms in this file are defined directly
by the universal property of mathlib's signed total complex. The filtration
keeps precisely the summands whose second degree is below a given bound. Every
fixed total degree is exhausted by a finite stage. No separate replacement
complex or totalization exactness hypothesis is introduced.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex₂

namespace Motivic.TorComparison

variable {C : Type*} [Category* C] [Preadditive C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ))
  [K.HasTotal (ComplexShape.down ℕ)]

/-- Projection from a total degree onto a specified bidegree. -/
noncomputable def firstQuadrantπ (n p q : ℕ) :
    (K.total (ComplexShape.down ℕ)).X n ⟶ (K.X p).X q :=
  K.totalDesc fun i j _ =>
    if hi : i = p then
      if hj : j = q then (K.XXIsoOfEq _ _ _ hi hj).hom else 0
    else 0

/-- Retain precisely the summands with vertical degree less than `r`. -/
noncomputable def firstQuadrantBelow (n r : ℕ) :
    (K.total (ComplexShape.down ℕ)).X n ⟶ (K.total (ComplexShape.down ℕ)).X n :=
  K.totalDesc fun i j h => if j < r then K.ιTotal (ComplexShape.down ℕ) i j n h else 0

@[reassoc (attr := simp)]
theorem firstQuadrant_ι_π (p q n : ℕ) (h : p + q = n) :
    K.ιTotal (ComplexShape.down ℕ) p q n h ≫ firstQuadrantπ K n p q = 𝟙 _ := by
  simp [firstQuadrantπ]

@[reassoc (attr := simp)]
theorem firstQuadrant_ι_π_of_ne_left (i j p q n : ℕ) (h : i + j = n) (hi : i ≠ p) :
    K.ιTotal (ComplexShape.down ℕ) i j n h ≫ firstQuadrantπ K n p q = 0 := by
  simp [firstQuadrantπ, hi]

@[reassoc (attr := simp)]
theorem firstQuadrant_ι_π_of_ne_right (i j p q n : ℕ) (h : i + j = n) (hj : j ≠ q) :
    K.ιTotal (ComplexShape.down ℕ) i j n h ≫ firstQuadrantπ K n p q = 0 := by
  simp [firstQuadrantπ, hj]

@[reassoc (attr := simp)]
theorem firstQuadrant_ι_below (i j n r : ℕ) (h : i + j = n) (hj : j < r) :
    K.ιTotal (ComplexShape.down ℕ) i j n h ≫ firstQuadrantBelow K n r =
      K.ιTotal (ComplexShape.down ℕ) i j n h := by
  simp [firstQuadrantBelow, hj]

@[reassoc (attr := simp)]
theorem firstQuadrant_ι_below_of_le (i j n r : ℕ) (h : i + j = n) (hj : r ≤ j) :
    K.ιTotal (ComplexShape.down ℕ) i j n h ≫ firstQuadrantBelow K n r = 0 := by
  simp [firstQuadrantBelow, Nat.not_lt.mpr hj]

@[simp]
theorem firstQuadrantBelow_zero (n : ℕ) : firstQuadrantBelow K n 0 = 0 := by
  apply total.hom_ext
  intro i j h
  simp

/-- Each diagonal is exhausted at its finite bound `n + 1`. -/
@[simp]
theorem firstQuadrantBelow_succ_self (n : ℕ) : firstQuadrantBelow K n (n + 1) = 𝟙 _ := by
  apply total.hom_ext
  intro i j h
  have hj : j < n + 1 := by change i + j = n at h; omega
  simp [hj]

/-- Moving one filtration step adds exactly one actual total-complex summand. -/
theorem firstQuadrantBelow_succ (p q n : ℕ) (h : p + q = n) :
    firstQuadrantBelow K n (q + 1) = firstQuadrantBelow K n q +
      firstQuadrantπ K n p q ≫ K.ιTotal (ComplexShape.down ℕ) p q n h := by
  apply total.hom_ext
  intro i j hij
  change i + j = n at hij
  by_cases hj : j = q
  · subst j
    have hi : i = p := by omega
    subst i
    simp [Preadditive.comp_add]
  · by_cases hjq : j < q
    · simp [Preadditive.comp_add, hj, hjq, show j < q + 1 by omega]
    · simp [Preadditive.comp_add, hj, show q ≤ j by omega, show q + 1 ≤ j by omega]

/-- A component above the retained filtration range vanishes. -/
@[reassoc (attr := simp)]
theorem firstQuadrantBelow_π_of_le (n r p q : ℕ) (h : r ≤ q) :
    firstQuadrantBelow K n r ≫ firstQuadrantπ K n p q = 0 := by
  apply total.hom_ext
  intro i j hij
  by_cases hj : j < r
  · simp [hj, show j ≠ q by omega]
  · simp [show r ≤ j by omega]

/-- A retained component is unchanged by the filtration projector. -/
@[reassoc (attr := simp)]
theorem firstQuadrantBelow_π (n r p q : ℕ) (h : q < r) :
    firstQuadrantBelow K n r ≫ firstQuadrantπ K n p q = firstQuadrantπ K n p q := by
  apply total.hom_ext
  intro i j hij
  by_cases hj : j < r
  · simp [hj]
  · simp [show r ≤ j by omega, show j ≠ q by omega]

end Motivic.TorComparison
