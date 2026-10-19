/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.TotalComplex.FirstQuadrantDifferential
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Acyclic rows give an acyclic first-quadrant total complex

A finite filtration of each actual total degree allows the usual staircase
argument to be performed without convergence or boundedness assumptions on the
whole bicomplex. The top remaining component of a cycle is a horizontal cycle;
a horizontal primitive removes it and introduces only lower vertical degrees.
Induction through the finitely many components proves exactness of mathlib's
literal signed total complex.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂

universe u

namespace ModuleCat.TorComparison

variable {R : Type u} [Ring R]
  (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ))
  [K.HasTotal (ComplexShape.down ℕ)]

/-- Above the retained vertical bound an element has zero components. -/
theorem firstQuadrant_component_eq_zero (n r p q : ℕ) (h : r ≤ q)
    (x : (K.total (ComplexShape.down ℕ)).X n)
    (hx : firstQuadrantBelow K n r x = x) : firstQuadrantπ K n p q x = 0 := by
  rw [← hx]
  exact ConcreteCategory.congr_hom (firstQuadrantBelow_π_of_le K n r p q h) x

/-- The top remaining component of a total cycle is a horizontal cycle. -/
theorem firstQuadrant_top_cycle (p q n : ℕ) (h : p + q = n)
    (x : (K.total (ComplexShape.down ℕ)).X n)
    (hx : (K.total (ComplexShape.down ℕ)).d n (n - 1) x = 0)
    (hb : firstQuadrantBelow K n (q + 1) x = x) :
    (K.d p (p - 1)).f q (firstQuadrantπ K n p q x) = 0 := by
  cases p with
  | zero =>
      rw [K.shape_f 0 0 (by simp)]
      rfl
  | succ p =>
      have hn : n - 1 + 1 = n := by omega
      have hd := firstQuadrant_d_π K p q (n - 1) (by omega)
      rw [hn] at hd
      have hzero := firstQuadrant_component_eq_zero K n (q + 1) p (q + 1)
        (le_refl _) x hb
      have he := ConcreteCategory.congr_hom hd x
      simpa [hx, hzero] using he.symm

/-- One horizontal primitive removes the top component of a genuine total cycle. -/
theorem firstQuadrant_clear_top (p q n : ℕ) (h : p + q = n)
    (hrow : (K.flip.X q).ExactAt p)
    (x : (K.total (ComplexShape.down ℕ)).X n)
    (hx : (K.total (ComplexShape.down ℕ)).d n (n - 1) x = 0)
    (hb : firstQuadrantBelow K n (q + 1) x = x) :
    ∃ y : (K.total (ComplexShape.down ℕ)).X (n + 1),
      (K.total (ComplexShape.down ℕ)).d n (n - 1)
        (x - (K.total (ComplexShape.down ℕ)).d (n + 1) n y) = 0 ∧
      firstQuadrantBelow K n q
        (x - (K.total (ComplexShape.down ℕ)).d (n + 1) n y) =
        x - (K.total (ComplexShape.down ℕ)).d (n + 1) n y := by
  rw [exactAt_iff' _ (p + 1) p (p - 1) (by simp) (by cases p <;> simp),
    ShortComplex.moduleCat_exact_iff] at hrow
  obtain ⟨z, hz⟩ := hrow (firstQuadrantπ K n p q x) (firstQuadrant_top_cycle K p q n h x hx hb)
  let y := K.ιTotal (ComplexShape.down ℕ) (p + 1) q (n + 1)
    (by change p + 1 + q = n + 1; omega) z
  have h₁ : firstQuadrantπ K (n + 1) (p + 1) q y = z :=
    ConcreteCategory.congr_hom (firstQuadrant_ι_π K (p + 1) q (n + 1) (by omega)) z
  have h₂ : firstQuadrantπ K (n + 1) p (q + 1) y = 0 :=
    ConcreteCategory.congr_hom (firstQuadrant_ι_π_of_ne_left K (p + 1) q p (q + 1)
      (n + 1) (by omega) (by omega)) z
  have hyπ : firstQuadrantπ K n p q ((K.total (ComplexShape.down ℕ)).d (n + 1) n y) =
      firstQuadrantπ K n p q x := by
    have hd := ConcreteCategory.congr_hom (firstQuadrant_d_π K p q n h) y
    have hd' : firstQuadrantπ K n p q
        ((K.total (ComplexShape.down ℕ)).d (n + 1) n y) = (K.d (p + 1) p).f q z := by
      simpa [h₁, h₂] using hd
    exact hd'.trans hz
  have hyb : firstQuadrantBelow K n (q + 1)
      ((K.total (ComplexShape.down ℕ)).d (n + 1) n y) =
      (K.total (ComplexShape.down ℕ)).d (n + 1) n y :=
    ConcreteCategory.congr_hom (firstQuadrant_ι_d_below K p q n h) z
  refine ⟨y, ?_, ?_⟩
  · rw [map_sub, hx]
    have hd : (K.total (ComplexShape.down ℕ)).d n (n - 1)
        ((K.total (ComplexShape.down ℕ)).d (n + 1) n y) = 0 :=
      ConcreteCategory.congr_hom ((K.total (ComplexShape.down ℕ)).d_comp_d
        (n + 1) n (n - 1)) y
    rw [hd, sub_self]
  · have hs := ConcreteCategory.congr_hom (firstQuadrantBelow_succ K p q n h)
      (x - (K.total (ComplexShape.down ℕ)).d (n + 1) n y)
    simpa [map_sub, hb, hyb, hyπ] using hs.symm

/-- A finite vertical support bound suffices for a cycle to be a boundary. -/
theorem firstQuadrant_boundary_of_below
    (hK : ∀ q, (K.flip.X q).Acyclic) (r n : ℕ) (hr : r ≤ n + 1)
    (x : (K.total (ComplexShape.down ℕ)).X n)
    (hx : (K.total (ComplexShape.down ℕ)).d n (n - 1) x = 0)
    (hb : firstQuadrantBelow K n r x = x) :
    ∃ y : (K.total (ComplexShape.down ℕ)).X (n + 1),
      (K.total (ComplexShape.down ℕ)).d (n + 1) n y = x := by
  induction r generalizing x with
  | zero =>
      have hx0 : x = 0 := by simpa using hb.symm
      exact ⟨0, by simp [hx0]⟩
  | succ r ih =>
      have hpr : n - r + r = n := by omega
      obtain ⟨y, hy, hyb⟩ := firstQuadrant_clear_top K (n - r) r n hpr
        (hK r (n - r)) x hx hb
      obtain ⟨z, hz⟩ := ih (by omega) _ hy hyb
      refine ⟨z + y, ?_⟩
      rw [map_add, hz, sub_add_cancel]

/-- Acyclic horizontal rows imply acyclicity of the actual signed total complex. -/
theorem firstQuadrant_total_acyclic (hK : ∀ q, (K.flip.X q).Acyclic) :
    (K.total (ComplexShape.down ℕ)).Acyclic := by
  intro n
  rw [exactAt_iff' _ (n + 1) n (n - 1) (by simp) (by cases n <;> simp),
    ShortComplex.moduleCat_exact_iff]
  intro x hx
  exact firstQuadrant_boundary_of_below K hK (n + 1) n (le_refl _) x hx
    (by rw [firstQuadrantBelow_succ_self]; rfl)

end ModuleCat.TorComparison
