/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Short exact sequences with acyclic kernel -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace HomologicalComplex

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}

/-- A short exact quotient by an all-degree acyclic complex is a quasi-isomorphism. -/
theorem quasiIso_of_shortExact_isZero_homology
    (S : ShortComplex (HomologicalComplex C c)) (hS : S.ShortExact)
    (hA : ∀ i, IsZero (S.X₁.homology i)) : QuasiIso S.g := by
  classical
  let T : ShortComplex (HomologicalComplex C c) :=
    ShortComplex.mk (0 : (0 : HomologicalComplex C c) ⟶ S.X₂) (𝟙 S.X₂) (by simp)
  have hT : T.ShortExact :=
    { exact := (T.exact_iff_mono rfl).2 inferInstance
      mono_f := by dsimp [T]; infer_instance
      epi_g := by dsimp [T]; infer_instance }
  let φ : T ⟶ S :=
    { τ₁ := 0
      τ₂ := 𝟙 _
      τ₃ := S.g
      comm₁₂ := by simp [T]
      comm₂₃ := by simp [T] }
  have h₁ : QuasiIso φ.τ₁ := by
    rw [quasiIso_iff]
    intro i
    apply (quasiIsoAt_iff_exactAt φ.τ₁ i ?_).2
    · exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2 (hA i)
    · rw [HomologicalComplex.exactAt_iff_isZero_homology]
      exact (HomologicalComplex.homologyFunctor C c i).map_isZero
          (_root_.CategoryTheory.Limits.isZero_zero _)
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃ φ hT hS h₁
    (by change QuasiIso (𝟙 S.X₂); infer_instance)

end HomologicalComplex
