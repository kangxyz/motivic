/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Nisnevich.FieldLifting
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Exact field evaluation for field-lifting topologies

Local surjectivity becomes surjectivity on sections over `Spec K`, since every
covering sieve there is maximal. This applies to any topology `J` coarser than
the field-lifting topology; the Nisnevich specialization is in
`Evaluation.lean`. For abelian-group-valued sheaves,
this proves that evaluation preserves epimorphisms and, together with left
exactness, preserves homology and exact sequences.

The abelian groups are in universe `u + 1` for the big site `Scheme.{u}`.
This makes the ordinary sheafification and local-surjectivity APIs available
without an unproved small-site replacement.

These are statements about sheaves and exact evaluation. They neither define
unbounded hypercohomology nor apply a bounded-below derived-functor API to the
bounded-above motivic complex.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v w

namespace AlgebraicGeometry.Nisnevich

variable (J : GrothendieckTopology Scheme.{u})

section Concrete

variable {A : Type v} [Category.{w} A] {FA : A → A → Type*} {CA : A → Type*}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]

/-- A locally surjective morphism of presheaves is surjective on field sections. -/
theorem surjective_app_of_isLocallySurjective_of_le (hJ : J ≤ fieldLiftingTopology)
    (K : Type u) [Field K]
    {F G : Scheme.{u}ᵒᵖ ⥤ A} (φ : F ⟶ G)
    [Presheaf.IsLocallySurjective J φ] :
    Function.Surjective (φ.app (op (Spec (.of K)))) := by
  intro s
  have htop := fieldLifting_covering_sieve_eq_top K
    (hJ _ (Presheaf.imageSieve_mem J φ s))
  have hi : Presheaf.imageSieve φ s (𝟙 _) := by rw [htop]; trivial
  obtain ⟨t, ht⟩ := hi
  exact ⟨t, by simpa using ht⟩

end Concrete

/-- Evaluation of abelian-group-valued sheaves at `Spec K`. -/
noncomputable def fieldEvaluation (K : Type u) [Field K] :
    Sheaf J AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  sheafToPresheaf J AddCommGrpCat ⋙
    (CategoryTheory.evaluation Scheme.{u}ᵒᵖ AddCommGrpCat).obj (op (Spec (.of K)))

instance (K : Type u) [Field K] : (fieldEvaluation J K).Additive := by
  unfold fieldEvaluation
  infer_instance

instance (K : Type u) [Field K] : PreservesFiniteLimits (fieldEvaluation J K) := by
  unfold fieldEvaluation
  infer_instance

/-- An epimorphism of abelian sheaves is surjective on field sections for a field-lifting site. -/
theorem surjective_app_of_epi_of_le (hJ : J ≤ fieldLiftingTopology) (K : Type u) [Field K]
    {F G : Sheaf J AddCommGrpCat.{u + 1}} (φ : F ⟶ G) [Epi φ] :
    Function.Surjective (φ.hom.app (op (Spec (.of K)))) := by
  have : Sheaf.IsLocallySurjective φ :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat φ).mpr inferInstance
  exact surjective_app_of_isLocallySurjective_of_le J hJ K φ.hom

/-- Evaluation on a field-lifting site preserves epimorphisms. -/
theorem fieldEvaluation_preservesEpimorphisms (hJ : J ≤ fieldLiftingTopology)
    (K : Type u) [Field K] : (fieldEvaluation J K).PreservesEpimorphisms where
  preserves φ _ := (AddCommGrpCat.epi_iff_surjective _).mpr (surjective_app_of_epi_of_le J hJ K φ)

/-- Field evaluation preserves kernels, cokernels, and hence homology. -/
theorem fieldEvaluation_preservesHomology (hJ : J ≤ fieldLiftingTopology)
    (K : Type u) [Field K] : (fieldEvaluation J K).PreservesHomology := by
  have := fieldEvaluation_preservesEpimorphisms J hJ K
  exact Functor.preservesHomology_of_preservesEpis_and_kernels (fieldEvaluation J K)

/-- Exact sequences of abelian sheaves on a field-lifting site stay exact at `Spec K`. -/
theorem exact_map_fieldEvaluation (hJ : J ≤ fieldLiftingTopology) (K : Type u) [Field K]
    (S : ShortComplex (Sheaf J AddCommGrpCat.{u + 1})) (hS : S.Exact) :
    (S.map (fieldEvaluation J K)).Exact := by
  have := fieldEvaluation_preservesHomology J hJ K
  exact hS.map (fieldEvaluation J K)

end AlgebraicGeometry.Nisnevich
