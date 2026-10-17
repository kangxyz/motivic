/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Scheme-theoretic disjoint unions of closed immersions -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology
universe u
namespace AlgebraicGeometry

/-- The coproduct preserves the entire scheme structures of disjoint closed subschemes. -/
theorem isClosedImmersion_coprod_desc {D Z C : Scheme.{u}}
    (i : D ⟶ C) (j : Z ⟶ C) [IsClosedImmersion i] [IsClosedImmersion j]
    (h : Disjoint (Set.range i) (Set.range j)) :
    IsClosedImmersion (coprod.desc i j) := by
  let q := coprod.desc i j
  have he : (q : (D ⨿ Z : Scheme) → C) ∘ coprodMk D Z = Sum.elim i j := by
    funext x
    cases x <;> simp [q, ← Scheme.Hom.comp_apply]
  refine { stalkMap_surjective := ?_, isClosedEmbedding := ?_ }
  · intro x
    obtain ⟨x | x, rfl⟩ := (coprodMk D Z).surjective x
    · rw [coprodMk_inl]
      have hs := i.stalkMap_surjective x
      rw [← coprod.inl_desc i j, Scheme.Hom.stalkMap_comp] at hs
      change Function.Surjective (((coprod.inl : D ⟶ D ⨿ Z).stalkMap x) ∘
        (coprod.desc i j).stalkMap ((coprod.inl : D ⟶ D ⨿ Z) x)) at hs
      exact hs.of_comp_left (ConcreteCategory.bijective_of_isIso
        ((coprod.inl : D ⟶ D ⨿ Z).stalkMap x)).injective
    · rw [coprodMk_inr]
      have hs := j.stalkMap_surjective x
      rw [← coprod.inr_desc i j, Scheme.Hom.stalkMap_comp] at hs
      change Function.Surjective (((coprod.inr : Z ⟶ D ⨿ Z).stalkMap x) ∘
        (coprod.desc i j).stalkMap ((coprod.inr : Z ⟶ D ⨿ Z) x)) at hs
      exact hs.of_comp_left (ConcreteCategory.bijective_of_isIso
        ((coprod.inr : Z ⟶ D ⨿ Z).stalkMap x)).injective
  · have hinj : Function.Injective (Sum.elim i j) := by
      intro a b hab
      cases a with
      | inl a =>
        cases b with
        | inl b => exact congrArg Sum.inl (i.isClosedEmbedding.injective hab)
        | inr b => exact False.elim (Set.disjoint_iff_forall_ne.mp h ⟨a, rfl⟩ ⟨b, rfl⟩ hab)
      | inr a =>
        cases b with
        | inl b => exact False.elim (Set.disjoint_iff_forall_ne.mp h ⟨b, rfl⟩ ⟨a, rfl⟩ hab.symm)
        | inr b => exact congrArg Sum.inr (j.isClosedEmbedding.injective hab)
    have hh := i.isClosedEmbedding.sumElim j.isClosedEmbedding hinj
    rw [← he] at hh
    convert hh.comp (coprodMk D Z).symm.isClosedEmbedding using 1
    funext x
    exact congrArg q ((coprodMk D Z).apply_symm_apply x).symm

end AlgebraicGeometry
