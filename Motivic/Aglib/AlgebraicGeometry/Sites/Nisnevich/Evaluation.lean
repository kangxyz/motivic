/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Nisnevich.Basic
public import Motivic.Aglib.AlgebraicGeometry.Sites.Nisnevich.FieldEvaluation

/-!
# Exact Nisnevich evaluation at a field

Local surjectivity becomes surjectivity on sections over `Spec K`, since every
Nisnevich covering sieve there is maximal. For abelian-group-valued sheaves,
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

section Concrete

variable {A : Type v} [Category.{w} A] {FA : A → A → Type*} {CA : A → Type*}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]

/-- A locally surjective morphism of presheaves is surjective on field sections. -/
theorem surjective_app_of_isLocallySurjective (K : Type u) [Field K]
    {F G : Scheme.{u}ᵒᵖ ⥤ A} (φ : F ⟶ G)
    [Presheaf.IsLocallySurjective topology φ] :
    Function.Surjective (φ.app (op (Spec (.of K)))) :=
  surjective_app_of_isLocallySurjective_of_le topology topology_le_fieldLiftingTopology K φ

end Concrete

/-- Evaluation of Nisnevich sheaves of abelian groups at `Spec K`. -/
noncomputable abbrev evaluation (K : Type u) [Field K] :
    Sheaf topology AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  fieldEvaluation topology K

/-- An epimorphism of abelian Nisnevich sheaves is surjective on field sections. -/
theorem surjective_app_of_epi (K : Type u) [Field K]
    {F G : Sheaf topology AddCommGrpCat.{u + 1}} (φ : F ⟶ G) [Epi φ] :
    Function.Surjective (φ.hom.app (op (Spec (.of K)))) :=
  surjective_app_of_epi_of_le topology topology_le_fieldLiftingTopology K φ

instance (K : Type u) [Field K] : (evaluation K).PreservesEpimorphisms :=
  fieldEvaluation_preservesEpimorphisms topology topology_le_fieldLiftingTopology K

/-- Field evaluation preserves kernels, cokernels, and hence homology. -/
instance (K : Type u) [Field K] : (evaluation K).PreservesHomology :=
  fieldEvaluation_preservesHomology topology topology_le_fieldLiftingTopology K

/-- Exact sequences of abelian Nisnevich sheaves stay exact at `Spec K`. -/
theorem exact_map_evaluation (K : Type u) [Field K]
    (S : ShortComplex (Sheaf topology AddCommGrpCat.{u + 1})) (hS : S.Exact) :
    (S.map (evaluation K)).Exact := hS.map (evaluation K)

end AlgebraicGeometry.Nisnevich
