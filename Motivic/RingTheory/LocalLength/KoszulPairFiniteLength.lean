/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.RingTheory.LocalLength.KoszulPairSymmetry
public import Motivic.RingTheory.LocalLength.ArtinianQuotient

/-!
# Annihilation and finite length of two-element Koszul homology

Both defining equations annihilate each of the three actual Koszul homology
modules, with no regularity hypothesis. For finite modules over a Noetherian
ring, an Artinian quotient by the two-generated ideal therefore proves finite
length of all three homology modules. This discharges local finiteness from
algebraic hypotheses rather than assuming the desired lengths are finite.
-/

@[expose] public section

universe u v

namespace Module.KoszulPair

variable {R : Type u} [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M] (a b : R)

/-- The first equation kills the actual degree-zero quotient. -/
theorem first_mem_annihilator_H₀ : a ∈ Module.annihilator R (H₀ M a b) := by
  apply Module.mem_annihilator.mpr
  intro x
  obtain ⟨x, rfl⟩ := (LinearMap.range (d₁ M a b)).mkQ_surjective x
  change (Submodule.Quotient.mk (a • x) : H₀ M a b) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact ⟨(x, 0), by simp⟩

/-- The second equation kills the actual degree-zero quotient. -/
theorem second_mem_annihilator_H₀ : b ∈ Module.annihilator R (H₀ M a b) := by
  apply Module.mem_annihilator.mpr
  intro x
  obtain ⟨x, rfl⟩ := (LinearMap.range (d₁ M a b)).mkQ_surjective x
  change (Submodule.Quotient.mk (b • x) : H₀ M a b) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact ⟨(0, x), by simp⟩

/-- Multiplying a one-cycle by the first equation is the boundary of its second coordinate. -/
theorem first_mem_annihilator_H₁ : a ∈ Module.annihilator R (H₁ M a b) := by
  apply Module.mem_annihilator.mpr
  intro x
  obtain ⟨x, rfl⟩ := (LinearMap.range (toCycles M a b)).mkQ_surjective x
  change (Submodule.Quotient.mk (a • x) : H₁ M a b) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨x.1.2, Subtype.ext (Prod.ext ?_ rfl)⟩
  change -(b • x.1.2) = a • x.1.1
  have hx : a • x.1.1 + b • x.1.2 = 0 := x.property
  exact (eq_neg_of_add_eq_zero_left hx).symm

/-- Multiplying a one-cycle by the second equation is the boundary of minus its first coordinate. -/
theorem second_mem_annihilator_H₁ : b ∈ Module.annihilator R (H₁ M a b) := by
  apply Module.mem_annihilator.mpr
  intro x
  obtain ⟨x, rfl⟩ := (LinearMap.range (toCycles M a b)).mkQ_surjective x
  change (Submodule.Quotient.mk (b • x) : H₁ M a b) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨-x.1.1, Subtype.ext (Prod.ext ?_ ?_)⟩
  · change -(b • -x.1.1) = b • x.1.1
    simp only [smul_neg, neg_neg]
  · change a • -x.1.1 = b • x.1.2
    rw [smul_neg]
    have hx : a • x.1.1 + b • x.1.2 = 0 := x.property
    exact (neg_eq_iff_add_eq_zero).mpr hx

/-- The first equation kills every degree-two cycle. -/
theorem first_mem_annihilator_H₂ : a ∈ Module.annihilator R (H₂ M a b) := by
  apply Module.mem_annihilator.mpr
  intro x
  apply Subtype.ext
  exact congrArg Prod.snd x.property

/-- The second equation kills every degree-two cycle. -/
theorem second_mem_annihilator_H₂ : b ∈ Module.annihilator R (H₂ M a b) := by
  apply Module.mem_annihilator.mpr
  intro x
  apply Subtype.ext
  exact neg_eq_zero.mp (congrArg Prod.fst x.property)

/-- The full two-generated ideal annihilates zeroth Koszul homology. -/
theorem span_le_annihilator_H₀ : Ideal.span ({a, b} : Set R) ≤
    Module.annihilator R (H₀ M a b) := by
  apply Ideal.span_le.mpr
  intro r hr
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with h | h
  · subst r
    exact first_mem_annihilator_H₀ M a b
  · subst r
    exact second_mem_annihilator_H₀ M a b

/-- The full two-generated ideal annihilates first Koszul homology. -/
theorem span_le_annihilator_H₁ : Ideal.span ({a, b} : Set R) ≤
    Module.annihilator R (H₁ M a b) := by
  apply Ideal.span_le.mpr
  intro r hr
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with h | h
  · subst r
    exact first_mem_annihilator_H₁ M a b
  · subst r
    exact second_mem_annihilator_H₁ M a b

/-- The full two-generated ideal annihilates second Koszul homology. -/
theorem span_le_annihilator_H₂ : Ideal.span ({a, b} : Set R) ≤
    Module.annihilator R (H₂ M a b) := by
  apply Ideal.span_le.mpr
  intro r hr
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with h | h
  · subst r
    exact first_mem_annihilator_H₂ M a b
  · subst r
    exact second_mem_annihilator_H₂ M a b

/-- An Artinian two-equation quotient gives finite length in degree zero. -/
theorem length_H₀_ne_top [IsNoetherianRing R] [Module.Finite R M]
    [IsArtinianRing (R ⧸ Ideal.span ({a, b} : Set R))] :
    Module.length R (H₀ M a b) ≠ ⊤ :=
  length_ne_top_of_artinian_quotient (H₀ M a b) (Ideal.span {a, b})
    (span_le_annihilator_H₀ M a b)

/-- An Artinian two-equation quotient gives finite length in degree one. -/
theorem length_H₁_ne_top [IsNoetherianRing R] [Module.Finite R M]
    [IsArtinianRing (R ⧸ Ideal.span ({a, b} : Set R))] :
    Module.length R (H₁ M a b) ≠ ⊤ :=
  length_ne_top_of_artinian_quotient (H₁ M a b) (Ideal.span {a, b})
    (span_le_annihilator_H₁ M a b)

/-- An Artinian two-equation quotient gives finite length in degree two. -/
theorem length_H₂_ne_top [IsNoetherianRing R] [Module.Finite R M]
    [IsArtinianRing (R ⧸ Ideal.span ({a, b} : Set R))] :
    Module.length R (H₂ M a b) ≠ ⊤ :=
  length_ne_top_of_artinian_quotient (H₂ M a b) (Ideal.span {a, b})
    (span_le_annihilator_H₂ M a b)

/-- Finite Koszul homology follows from a finite module and an Artinian equation quotient.
Neither scalar is assumed regular on the ring or on the module. -/
theorem hasFiniteHomology_of_artinian_quotient [IsNoetherianRing R] [Module.Finite R M]
    [IsArtinianRing (R ⧸ Ideal.span ({a, b} : Set R))] : HasFiniteHomology M a b :=
  ⟨length_H₀_ne_top M a b, length_H₁_ne_top M a b, length_H₂_ne_top M a b⟩

end Module.KoszulPair
