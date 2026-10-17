/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.TorComparison.FirstQuadrantCoordinates

/-!
# The signed first-quadrant differential in actual summand coordinates

Projecting the genuine total differential to bidegree `(p,q)` gives the
horizontal differential from `(p+1,q)` plus `(-1)^p` times the vertical
differential from `(p,q+1)`. These identities also verify the filtration
support needed for the finite cycle-clearing argument.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex₂

namespace Motivic.TorComparison

variable {C : Type*} [Category* C] [Preadditive C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ))
  [K.HasTotal (ComplexShape.down ℕ)]

@[reassoc]
theorem firstQuadrant_ι_d (i j n m : ℕ) (h : i + j = n) :
    K.ιTotal (ComplexShape.down ℕ) i j n h ≫ (K.total (ComplexShape.down ℕ)).d n m =
      K.d₁ (ComplexShape.down ℕ) i j m + K.d₂ (ComplexShape.down ℕ) i j m := by
  change _ ≫ (_ + _) = _
  rw [Preadditive.comp_add, K.ι_D₁, K.ι_D₂]

/-- The horizontal part of the total differential in component coordinates. -/
@[reassoc]
theorem firstQuadrant_D₁_π (p q n : ℕ) (h : p + q = n) :
    K.D₁ (ComplexShape.down ℕ) (n + 1) n ≫ firstQuadrantπ K n p q =
      firstQuadrantπ K (n + 1) (p + 1) q ≫ (K.d (p + 1) p).f q := by
  apply total.hom_ext
  intro i j hij
  change i + j = n + 1 at hij
  rw [K.ι_D₁_assoc]
  cases i with
  | zero =>
      rw [K.d₁_eq_zero _ _ _ _ (by simp), Limits.zero_comp]
      simp
  | succ i =>
      have hi : i + j = n := by omega
      rw [K.d₁_eq _ (show (ComplexShape.down ℕ).Rel (i + 1) i from rfl) j n hi]
      rw [show ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) (i + 1, j) = 1 from rfl, one_smul, Category.assoc]
      by_cases hj : j = q
      · subst j
        have hip : i = p := by omega
        subst i
        simp
      · simp [hj]

/-- The vertical part carries the genuine Koszul sign of the first degree. -/
@[reassoc]
theorem firstQuadrant_D₂_π (p q n : ℕ) (h : p + q = n) :
    K.D₂ (ComplexShape.down ℕ) (n + 1) n ≫ firstQuadrantπ K n p q =
      (-1 : ℤˣ) ^ p •
        (firstQuadrantπ K (n + 1) p (q + 1) ≫ (K.X p).d (q + 1) q) := by
  apply total.hom_ext
  intro i j hij
  change i + j = n + 1 at hij
  rw [K.ι_D₂_assoc, Linear.comp_units_smul]
  cases j with
  | zero =>
      rw [K.d₂_eq_zero _ _ _ _ (by simp), Limits.zero_comp]
      simp
  | succ j =>
      have hj : i + j = n := by omega
      rw [K.d₂_eq _ i (show (ComplexShape.down ℕ).Rel (j + 1) j from rfl) n hj]
      rw [Linear.units_smul_comp, Category.assoc]
      by_cases hi : i = p
      · subst i
        have hjq : j = q := by omega
        subst j
        simp
      · simp [hi]

/-- The complete signed total differential in component coordinates. -/
@[reassoc]
theorem firstQuadrant_d_π (p q n : ℕ) (h : p + q = n) :
    (K.total (ComplexShape.down ℕ)).d (n + 1) n ≫ firstQuadrantπ K n p q =
      firstQuadrantπ K (n + 1) (p + 1) q ≫ (K.d (p + 1) p).f q +
      (-1 : ℤˣ) ^ p •
        (firstQuadrantπ K (n + 1) p (q + 1) ≫ (K.X p).d (q + 1) q) := by
  change (_ + _) ≫ _ = _
  rw [Preadditive.add_comp, firstQuadrant_D₁_π K p q n h, firstQuadrant_D₂_π K p q n h]

/-- Clearing a component horizontally creates no components at a higher vertical degree. -/
@[reassoc]
theorem firstQuadrant_ι_d_below (p q n : ℕ) (h : p + q = n) :
    K.ιTotal (ComplexShape.down ℕ) (p + 1) q (n + 1) (by change p + 1 + q = n + 1; omega) ≫
        (K.total (ComplexShape.down ℕ)).d (n + 1) n ≫ firstQuadrantBelow K n (q + 1) =
      K.ιTotal (ComplexShape.down ℕ) (p + 1) q (n + 1) (by change p + 1 + q = n + 1; omega) ≫
        (K.total (ComplexShape.down ℕ)).d (n + 1) n := by
  rw [firstQuadrant_ι_d_assoc, firstQuadrant_ι_d, Preadditive.add_comp]
  rw [K.d₁_eq _ (show (ComplexShape.down ℕ).Rel (p + 1) p from rfl) q n h]
  rw [show ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
    (ComplexShape.down ℕ) (p + 1, q) = 1 from rfl]
  simp only [one_smul, Category.assoc, firstQuadrant_ι_below K p q n (q + 1) h (by omega)]
  congr 1
  cases q with
  | zero => rw [K.d₂_eq_zero (ComplexShape.down ℕ) (p + 1) 0 n (by simp), Limits.zero_comp]
  | succ q =>
      rw [K.d₂_eq _ (p + 1) (show (ComplexShape.down ℕ).Rel (q + 1) q from rfl) n
        (by change p + 1 + q = n; omega)]
      simp [Linear.units_smul_comp, Category.assoc]

end Motivic.TorComparison
