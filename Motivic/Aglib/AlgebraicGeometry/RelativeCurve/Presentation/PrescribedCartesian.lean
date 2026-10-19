/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Presentation.PrescribedLift

/-! # The retained prescribed scheme is the literal pullback of the full original scheme -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurve

/-- The retained full original scheme is Cartesian, including all nilpotents; it is
not merely a finite scheme having the correct underlying closed set. -/
theorem prescribedBaseToRetained_isPullback
    {X N Z S : Scheme.{u}} (i : X ⟶ N) [IsOpenImmersion i]
    (q : N ⟶ S) (f : X ⟶ S) (hi : i ≫ q = f)
    (T : S.Opens) (V : N.Opens) (hV : (V : Set N) ⊆ Set.range i)
    (z : Z ⟶ X) (hz : ∀ x : Z, (z ≫ f) x ∈ T → i (z x) ∈ V) :
    IsPullback ((z ≫ f) ⁻¹ᵁ T).ι (prescribedBaseToRetained i q f hi T V hV z hz)
      z (retainedBaseToOriginal i q T V hV) := by
  apply IsPullback.flip
  apply IsOpenImmersion.isPullback _ _ _ _
    (prescribedBaseToRetained_original i q f hi T V hV z hz).symm
  ext y
  simp only [Scheme.Opens.opensRange_ι]
  change z y ∈ Set.range (retainedBaseToOriginal i q T V hV) ↔ (z ≫ f) y ∈ T
  constructor
  · rintro ⟨x, hx⟩
    change f (z y) ∈ T
    rw [← hx, ← hi]
    change q ((retainedBaseToOriginal i q T V hV ≫ i) x) ∈ T
    rw [retainedBaseToOriginal_comp]
    exact x.property
  · intro hy
    exact prescribedBase_range_original i q f hi T V hV z hz ⟨⟨y, hy⟩, rfl⟩

end AlgebraicGeometry.Scheme.RelativeCurve
