/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.OriginalGermTupleSheaf

/-! # Surjective actual open restrictions of the original germ-tuple sheaf -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Opposite AlgebraicGeometry
universe u
namespace Motivic.PresheafWithTransfers
variable (k : Type u) [Field k] (P : PresheafWithTransfers.{u + 1} k)
  (hP : Presheaf.IsSheaf (SmoothSite.nisnevichTopology (Spec (.of k))) ((toPresheaf k).obj P))
  {U X : SmoothSite (Spec (.of k))}
set_option quotPrecheck false in
local notation "F" => ((toPresheaf k).obj P)
set_option quotPrecheck false in
local notation "G" => ((toPresheaf k).obj (originalGermTuplePresheaf k P hP))

/-- A tuple of original germs on an actual open subscheme extends by independent
choices at its image points and zero elsewhere. This is a surjectivity result,
not a claim of ordinary Nisnevich cohomological acyclicity. -/
theorem originalGermTuple_openRestriction_surjective (j : U ⟶ X)
    [IsOpenImmersion j.left] : Function.Surjective ((G).map j.op) := by
  classical
  intro s
  have hx : ∀ x : X.left, ∃ b : (SmoothSite.nisnevichPointFiberCocone X x F).pt,
      ∀ t : originalGermTuples k P (Cor.mk X), t x = b →
        ∀ y : U.left, j.left y = x → ((G).map j.op t) y = s y := by
    intro x
    by_cases h : ∃ y : U.left, j.left y = x
    · obtain ⟨y, rfl⟩ := h
      let e := SmoothSite.originalGermEtaleIso.{u, 0} F j y
      refine ⟨e.inv (s y), ?_⟩
      intro t ht z hz
      have he : z = y := j.left.isOpenEmbedding.injective hz
      subst z
      rw [originalGermTuplePresheaf_map_apply, ht]
      exact ConcreteCategory.congr_hom e.inv_hom_id (s y)
    · refine ⟨0, ?_⟩
      intro t ht y hy
      exact (h ⟨y, hy⟩).elim
  choose b hb using hx
  refine ⟨b, ?_⟩
  funext y
  exact hb (j.left y) b rfl y rfl

end Motivic.PresheafWithTransfers
