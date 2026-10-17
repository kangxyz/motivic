/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.RetainedEtaleClosedSquare

/-! # The original punctured complement on the actual retained affine target -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurve
variable {X N Z S A : Scheme.{u}} (i : X ⟶ N) [IsOpenImmersion i]
  (q : N ⟶ S) (f : X ⟶ S) (hi : i ≫ q = f)
  (T : S.Opens) (V : N.Opens) (hV : (V : Set N) ⊆ Set.range i)
  (z : Z ⟶ X) (hz : ∀ x : Z, (z ≫ f) x ∈ T → i (z x) ∈ V)
  (a : A ⟶ X) [IsOpenImmersion a]

omit [IsOpenImmersion a] in
/-- The original puncture and original full prescribed scheme remain disjoint. -/
theorem retainedPunctured_disjoint (ha : Disjoint (Set.range a) (Set.range z)) :
    Disjoint (Set.range (pullback.snd a (retainedBaseToOriginal i q T V hV)))
      (Set.range (prescribedBaseToRetained i q f hi T V hV z hz)) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ ⟨y, he⟩
  have h1 := congrArg (fun f => f x)
    (pullback.condition (f := a) (g := retainedBaseToOriginal i q T V hV))
  have h2 := congrArg (fun f => f y) (prescribedBaseToRetained_original i q f hi T V hV z hz)
  have h3 := congrArg (retainedBaseToOriginal i q T V hV) he
  exact Set.disjoint_iff_forall_ne.mp ha ⟨_, rfl⟩ ⟨_, rfl⟩
    (h1.trans (h3.symm.trans h2))

/-- The actual retained target is covered by the unchanged puncture and full base-restricted Z. -/
theorem retainedPunctured_cover (hcover : ∀ x : X, x ∈ Set.range a ∨ x ∈ Set.range z) :
    ∀ x : (retainedBaseOpen q T V).toScheme,
      x ∈ Set.range (pullback.snd a (retainedBaseToOriginal i q T V hV)) ∨
      x ∈ Set.range (prescribedBaseToRetained i q f hi T V hV z hz) := by
  intro x
  rcases hcover (retainedBaseToOriginal i q T V hV x) with ha | hz'
  · left
    rw [IsOpenImmersion.range_pullbackSnd]
    exact ha
  · obtain ⟨y, hy⟩ := hz'
    have hym : (z ≫ f) y ∈ T := by
      change f (z y) ∈ T
      rw [hy, ← hi]
      change q (i (retainedBaseToOriginal i q T V hV x)) ∈ T
      have he := congrArg (fun f => f x) (retainedBaseToOriginal_comp i q T V hV)
      change q ((retainedBaseToOriginal i q T V hV ≫ i) x) ∈ T
      rw [he]
      exact x.property
    right
    refine ⟨⟨y, hym⟩, ?_⟩
    apply (retainedBaseToOriginal i q T V hV).isOpenEmbedding.injective
    have he := congrArg (fun f => f ⟨y, hym⟩)
      (prescribedBaseToRetained_original i q f hi T V hV z hz)
    exact he.trans hy

end AlgebraicGeometry.Scheme.RelativeCurve
