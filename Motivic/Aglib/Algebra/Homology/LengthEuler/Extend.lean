/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.LengthEuler.Basic
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-!
# Length Euler sums under extension of complex shapes

Extending an actual complex by zero preserves finite-length homology. Its
homology support is precisely the image of the original support. Consequently,
its signed Euler sum is the original Euler sum with the signs reindexed along
the embedding. The proof uses the actual extension homology isomorphisms and
finite sums over the genuine homology support.
-/

@[expose] public section

open CategoryTheory

universe u v w w'

namespace HomologicalComplex.ModuleLengthEuler

variable {R : Type u} [Ring R] {ι : Type w} {ι' : Type w'}
variable {c : ComplexShape ι} {c' : ComplexShape ι'}
variable (K : HomologicalComplex (ModuleCat.{v} R) c) (e : c.Embedding c')

/-- Extension identifies the homology lengths in every degree in the image. -/
theorem length_homology_extend_image (i : ι) :
    Module.length R ((K.extend e).homology (e.f i)) = Module.length R (K.homology i) :=
  (K.extendHomologyIso e rfl).toLinearEquiv.length_eq

/-- Extension has zero homology length outside the image of the embedding. -/
theorem length_homology_extend_outside (j : ι') (hj : ∀ i, e.f i ≠ j) :
    Module.length R ((K.extend e).homology j) = 0 := by
  have : Subsingleton ((K.extend e).homology j) :=
    ModuleCat.isZero_iff_subsingleton.mp
      ((HomologicalComplex.exactAt_iff_isZero_homology _ _).mp (K.extend_exactAt e j hj))
  exact Module.length_eq_zero

/-- The actual nonzero homology support is exactly reindexed by extension. -/
theorem support_length_homology_extend :
    Function.support (fun j => Module.length R ((K.extend e).homology j)) =
      e.f '' Function.support (fun i => Module.length R (K.homology i)) := by
  ext j
  constructor
  · intro hj
    by_cases h : ∃ i, e.f i = j
    · obtain ⟨i, rfl⟩ := h
      refine ⟨i, ?_, rfl⟩
      simpa only [Function.mem_support, length_homology_extend_image] using hj
    · exact (hj (length_homology_extend_outside K e j (by simpa using h))).elim
  · rintro ⟨i, hi, rfl⟩
    simpa only [Function.mem_support, length_homology_extend_image] using hi

variable {K}

/-- Actual finite-length homology survives extension by zero. -/
theorem FiniteHomology.extend (hK : FiniteHomology K) : FiniteHomology (K.extend e) where
  finite_length j := by
    by_cases hj : ∃ i, e.f i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [length_homology_extend_image]
      exact hK.finite_length i
    · rw [length_homology_extend_outside K e j (by simpa using hj)]
      simp
  finite_support := by
    rw [support_length_homology_extend]
    exact hK.finite_support.image e.f

/-- The signed Euler sum of an extension is reindexed along its actual embedding. -/
theorem homologyEuler_extend (sign : ι' → ℤ) (hK : FiniteHomology K) :
    homologyEuler (K.extend e) sign (hK.extend e) =
      homologyEuler K (fun i => sign (e.f i)) hK := by
  classical
  let s := hK.finite_support.toFinset
  have hs : Function.support (fun i => Module.length R (K.homology i)) ⊆ s := by
    intro i hi
    exact hK.finite_support.mem_toFinset.mpr hi
  have hse : Function.support (fun j => Module.length R ((K.extend e).homology j)) ⊆
      s.image e.f := by
    rw [support_length_homology_extend]
    rintro j ⟨i, hi, rfl⟩
    exact Finset.mem_image.mpr ⟨i, hs hi, rfl⟩
  change signedLengthSum _ _ _ = signedLengthSum _ _ _
  rw [signedLengthSum_eq_sum _ sign (hK.extend e) (s.image e.f) hse,
    signedLengthSum_eq_sum _ _ hK s hs, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integerLength_eq_of_equiv (K.extendHomologyIso e rfl).toLinearEquiv]
  · intro i _ j _ hij
    exact e.injective_f hij

end HomologicalComplex.ModuleLengthEuler
