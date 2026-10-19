/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Presentation.Basic

/-! # Original presentations under an actual ambient isomorphism

Only the ambient coordinate model changes. The retained curve, complete bad
boundary and full closed scheme remain the same; the étale pullback is changed
through its canonical Cartesian comparison.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation

variable {k : Type u} [Field k] {X X' Y A Z : Scheme.{u}}
  {b : X ⟶ Spec (.of k)} {p : Y ⟶ X} {a : A ⟶ X}
  {z : Z ⟶ X} {s : Z ⟶ Y} {x : X}

/-- The original pullback remains Cartesian after an ambient coordinate isomorphism. -/
theorem ambientIso_pullback
    {T : Scheme.{u}} (p : Y ⟶ X) (r : T ⟶ X) (i : X ≅ X') :
    IsPullback (pullback.fst p r) (pullback.snd p r) (p ≫ i.hom) (r ≫ i.hom) := by
  apply (IsPullback.of_hasPullback p r).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) i <;> simp

/-- A presentation retains all original data under an explicit ambient coordinate isomorphism. -/
def mapAmbientIso (e : OriginalEtalePresentation k b p a z s x) (i : X ≅ X') :
    OriginalEtalePresentation k (i.inv ≫ b) (p ≫ i.hom) (a ≫ i.hom)
      (z ≫ i.hom) s (i.hom x) := by
  let H := ambientIso_pullback p e.refinement i
  let c := H.isoPullback
  let Ha := ambientIso_pullback a e.refinement i
  have harange :
      Set.range (pullback.snd (a ≫ i.hom) (e.refinement ≫ i.hom)) =
        Set.range (pullback.snd a e.refinement) := by
    ext t
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨Ha.isoPullback.inv v, congrArg (fun f => f v) Ha.isoPullback_inv_snd⟩
    · rintro ⟨v, rfl⟩
      exact ⟨Ha.isoPullback.hom v, congrArg (fun f => f v) Ha.isoPullback_hom_snd⟩
  have : IsOpenImmersion e.refinement := e.refinement_open
  have : IsClosedImmersion e.closedLift := e.closedLift_closed
  have : IsFinite ((pullback.snd p e.refinement) ∣_ e.goodOpen) := e.good_finite
  refine {
    e with
    refinement := e.refinement ≫ i.hom
    refinement_open := inferInstance
    point_eq := ?_
    base_compatibility := ?_
    closed_cartesian := ?_
    closedLift := e.closedLift ≫ c.hom
    closedLift_original := ?_
    closedLift_eq := ?_
    closedLift_closed := inferInstance
    closedLift_cartesian := ?_
    punctured_disjoint := ?_
    punctured_cover := ?_
    good_finite := ?_ }
  · change i.hom (e.refinement e.point) = i.hom x
    rw [e.point_eq]
  · simpa only [Category.assoc, Iso.hom_inv_id_assoc] using e.base_compatibility
  · apply e.closed_cartesian.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) i <;> simp
  · rw [Category.assoc, H.isoPullback_hom_fst]
    exact e.closedLift_original
  · rw [Category.assoc, H.isoPullback_hom_snd]
    exact e.closedLift_eq
  · apply e.closedLift_cartesian.of_iso (Iso.refl _) c (Iso.refl _) (Iso.refl _)
    · simp
    · simp
    · simpa only [Iso.refl_hom, Category.comp_id] using H.isoPullback_hom_snd.symm
    · simp
  · rw [harange]
    exact e.punctured_disjoint
  · intro t
    rw [harange]
    exact e.punctured_cover t
  · rw [← H.isoPullback_inv_snd, morphismRestrict_comp]
    infer_instance

/-- The source of the original étale map may be identified through an actual
isomorphism, retaining its original section and complete finite-good locus. -/
def mapEtaleIso (e : OriginalEtalePresentation k b p a z s x)
    {Y' : Scheme.{u}} (i : Y ≅ Y') :
    OriginalEtalePresentation k b (i.inv ≫ p) a z (s ≫ i.hom) x := by
  have H : IsPullback (pullback.fst p e.refinement ≫ i.hom)
      (pullback.snd p e.refinement) (i.inv ≫ p) e.refinement := by
    apply (IsPullback.of_hasPullback p e.refinement).of_iso
      (Iso.refl _) i (Iso.refl _) (Iso.refl _) <;> simp
  let c := H.isoPullback
  have : IsClosedImmersion e.closedLift := e.closedLift_closed
  have : IsFinite ((pullback.snd p e.refinement) ∣_ e.goodOpen) := e.good_finite
  refine {
    e with
    closedLift := e.closedLift ≫ c.hom
    closedLift_original := ?_
    closedLift_eq := ?_
    closedLift_closed := inferInstance
    closedLift_cartesian := ?_
    good_finite := ?_ }
  · rw [Category.assoc, H.isoPullback_hom_fst, ← Category.assoc,
      e.closedLift_original, Category.assoc]
  · rw [Category.assoc, H.isoPullback_hom_snd]
    exact e.closedLift_eq
  · apply e.closedLift_cartesian.of_iso (Iso.refl _) c (Iso.refl _) (Iso.refl _)
    · simp
    · simp
    · simpa only [Iso.refl_hom, Category.comp_id] using H.isoPullback_hom_snd.symm
    · simp
  · rw [← H.isoPullback_inv_snd, morphismRestrict_comp]
    infer_instance

/-- Replacing an open immersion by the same actual open does not change the
presentation's prescribed scheme or any étale lifting data. -/
def withPuncture (e : OriginalEtalePresentation k b p a z s x)
    [IsOpenImmersion a] {A' : Scheme.{u}} (a' : A' ⟶ X) [IsOpenImmersion a']
    (ha : Set.range a' = Set.range a) :
    OriginalEtalePresentation k b p a' z s x := by
  have hr : Set.range (pullback.snd a' e.refinement) =
      Set.range (pullback.snd a e.refinement) := by
    rw [IsOpenImmersion.range_pullbackSnd, IsOpenImmersion.range_pullbackSnd]
    change e.refinement ⁻¹' Set.range a' = e.refinement ⁻¹' Set.range a
    rw [ha]
  exact {
    e with
    punctured_disjoint := hr.symm ▸ e.punctured_disjoint
    punctured_cover := fun t => hr.symm ▸ e.punctured_cover t }

end AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation
