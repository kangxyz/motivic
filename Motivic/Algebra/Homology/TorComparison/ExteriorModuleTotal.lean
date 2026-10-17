/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.TorComparison.ExteriorModuleFunctor
public import Mathlib.Algebra.Homology.Bifunctor

/-!
# Projectivity of exterior total-complex terms

Each term of the actual signed exterior total complex is its specified coproduct
of exterior tensor modules. Lifts on summands assemble using the actual total
coproduct. The proof allows arbitrary index universes. This proves degreewise projectivity only;
exactness of the augmentation is a separate prerequisite.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u

namespace Motivic.TorComparison.ExteriorModule

variable (k U V : Type u) [CommRing k] [CommRing U] [CommRing V]
  [Algebra k U] [Algebra k V]
  {I₁ I₂ J : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  (c : ComplexShape J) [DecidableEq J] [TotalComplexShape c₁ c₂ c]

/-- Every actual exterior total term of two degreewise projective complexes is projective. -/
theorem projective_total_X (K₁ : HomologicalComplex (ModuleCat.{u} U) c₁)
    (K₂ : HomologicalComplex (ModuleCat.{u} V) c₂)
    [∀ i, CategoryTheory.Projective (K₁.X i)] [∀ i, CategoryTheory.Projective (K₂.X i)]
    [HasMapBifunctor K₁ K₂ (bifunctor k U V) c] (n : J) :
    CategoryTheory.Projective ((mapBifunctor K₁ K₂ (bifunctor k U V) c).X n) := by
  have (i₁ : I₁) (i₂ : I₂) :
      CategoryTheory.Projective (((bifunctor k U V).obj (K₁.X i₁)).obj (K₂.X i₂)) :=
    projective_obj k U V _ _
  refine ⟨?_⟩
  intro E X f e he
  refine ⟨mapBifunctorDesc (fun i₁ i₂ h ↦ CategoryTheory.Projective.factorThru
    (ιMapBifunctor K₁ K₂ (bifunctor k U V) c i₁ i₂ n h ≫ f) e), ?_⟩
  apply mapBifunctor.hom_ext
  intro i₁ i₂ h
  simp only [ι_mapBifunctorDesc_assoc, CategoryTheory.Projective.factorThru_comp]

end Motivic.TorComparison.ExteriorModule
