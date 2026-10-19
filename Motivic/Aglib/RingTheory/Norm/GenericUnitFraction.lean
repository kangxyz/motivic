/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.PolynomialFiberNorm
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.Algebra.Module.Torsion.Free

/-!
# Base-denominator fractions for units of the whole generic algebra

A unit of the actual generic tensor algebra has a regular numerator and a
regular denominator coming from the original base. No component decomposition
or domain hypothesis on the finite algebra is required.


Intended upstream module: `Aglib.RingTheory.Norm.GenericUnitFraction`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberChartNorm`.
-/

@[expose] public noncomputable section

open scoped TensorProduct nonZeroDivisors

namespace Algebra

variable {A B K : Type*} [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
  [Field K] [Algebra A K] [IsFractionRing A K] [Module.IsTorsionFree A B]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- A unit of the whole generic tensor algebra admits a regular fraction whose
denominator is a nonzero element of the original base. -/
theorem exists_regular_base_fraction_of_isUnit (h : K ⊗[A] B) (hh : IsUnit h) :
    ∃ (a : B) (s : A), s ≠ 0 ∧ a ∈ nonZeroDivisors B ∧
      algebraMap A B s ∈ nonZeroDivisors B ∧
      h * ((1 : K) ⊗ₜ[A] algebraMap A B s) = (1 : K) ⊗ₜ[A] a := by
  have hbase (s : A) (hs : s ≠ 0) : algebraMap A B s ∈ nonZeroDivisors B := by
    rw [mem_nonZeroDivisors_iff_left]
    intro b hb
    have he : s • b = 0 := by simpa only [Algebra.smul_def] using hb
    exact (smul_eq_zero.mp he).resolve_left hs
  have hden : Algebra.algebraMapSubmonoid B (nonZeroDivisors A) ≤ nonZeroDivisors B := by
    rintro _ ⟨s, hs, rfl⟩
    exact hbase s (nonZeroDivisors.ne_zero hs)
  have hi : Function.Injective (algebraMap B (K ⊗[A] B)) :=
    IsLocalization.injective (K ⊗[A] B) hden
  obtain ⟨⟨a, s⟩, he⟩ :=
    IsLocalizedModule.surj (nonZeroDivisors A) (TensorProduct.mk A K B 1) h
  have he' : h * ((1 : K) ⊗ₜ[A] algebraMap A B (s : A)) = (1 : K) ⊗ₜ[A] a := by
    simpa only [TensorProduct.mk_apply, Submonoid.smul_def, Algebra.smul_def,
      IsScalarTower.algebraMap_apply A B
      (K ⊗[A] B), Algebra.TensorProduct.right_algebraMap_apply, mul_comm] using he
  have hu : IsUnit (algebraMap B (K ⊗[A] B) (algebraMap A B (s : A))) :=
    IsLocalization.map_units (M := Algebra.algebraMapSubmonoid B (nonZeroDivisors A))
      (K ⊗[A] B)
      ⟨algebraMap A B (s : A), ⟨s, s.property, rfl⟩⟩
  have ha : a ∈ nonZeroDivisors B := by
    apply mem_nonZeroDivisors_of_injective hi
    have hau : IsUnit (algebraMap B (K ⊗[A] B) a) := by
      rw [Algebra.TensorProduct.right_algebraMap_apply, ← he']
      exact hh.mul hu
    exact hau.mem_nonZeroDivisors
  exact ⟨a, s, nonZeroDivisors.ne_zero s.property, ha,
    hbase s (nonZeroDivisors.ne_zero s.property), he'⟩

/-- The same generic unit has the exact ratio of original determinant norms,
with regular numerator and base denominator. -/
theorem exists_regular_base_fraction_norm [Module.Finite A B] [Module.Free A B]
    (h : K ⊗[A] B) (hh : IsUnit h) :
    ∃ (a : B) (s : A), s ≠ 0 ∧ a ∈ nonZeroDivisors B ∧
      algebraMap A B s ∈ nonZeroDivisors B ∧
      h * ((1 : K) ⊗ₜ[A] algebraMap A B s) = (1 : K) ⊗ₜ[A] a ∧
      norm K h = algebraMap A K (norm A a) /
        algebraMap A K (norm A (algebraMap A B s)) := by
  obtain ⟨a, s, hs, ha, hb, he⟩ := exists_regular_base_fraction_of_isUnit h hh
  refine ⟨a, s, hs, ha, hb, he, ?_⟩
  have hu : IsUnit ((1 : K) ⊗ₜ[A] algebraMap A B s) := by
    exact IsLocalization.map_units (M := Algebra.algebraMapSubmonoid B (nonZeroDivisors A))
      (K ⊗[A] B)
      ⟨algebraMap A B s, ⟨s, mem_nonZeroDivisors_iff_ne_zero.mpr hs, rfl⟩⟩
  have hn : algebraMap A K (norm A (algebraMap A B s)) ≠ 0 := by
    rw [← norm_one_tmul (A := K)]
    exact (hu.map (norm K)).ne_zero
  apply (eq_div_iff hn).mpr
  have hn' := congrArg (norm K) he
  simpa only [map_mul, norm_one_tmul] using hn'

end Algebra
