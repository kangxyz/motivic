/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.Projection
public import Mathlib.AlgebraicGeometry.Pullbacks
/-! # Whole-cylinder comparison from a Cartesian square

This universal-property argument is independent of affine coordinates, opens,
coefficient rings, and representatives.

Intended upstream module:
`Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.CartesianCylinderIso`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`AffineLine.NativeOriginalCylinder`.
-/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite
variable (R : CommRingCat.{u})
  {U U' T T' : SmoothSite (Spec R)}
  (l : U' ⟶ U) (h : T' ⟶ T) (q' : T' ⟶ U')
  (e : T ≅ a1Cylinder R U)
  (H : IsPullback h.left q'.left (e.hom ≫ a1Projection R U).left l.left)

include l H

/-- Pasting the Cartesian restriction with the original product square. -/
theorem cartesianCylinder_isPullback :
    IsPullback q'.left
      (h.left ≫ e.hom.left ≫ pullback.snd U.hom (polynomialProjection R))
      U'.hom (polynomialProjection R) := by
  have H' : IsPullback (h.left ≫ e.hom.left) q'.left
      (pullback.fst U.hom (polynomialProjection R)) l.left := by
    apply H.of_iso (Iso.refl _) ((forgetScheme (Spec R)).mapIso e)
      (Iso.refl _) (Iso.refl _)
    · simp only [Iso.refl_hom]
      rfl
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    · simp only [Iso.refl_hom, Category.comp_id]
      rfl
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  simpa only [Category.assoc, MorphismProperty.Over.w] using
    H'.flip.paste_vert (IsPullback.of_hasPullback U.hom (polynomialProjection R))

/-- The canonical comparison identifies the entire Cartesian restriction with
an entire cylinder, preserving both projections. -/
def cartesianCylinderIso : T' ≅ a1Cylinder R U' :=
  MorphismProperty.Over.isoMk (cartesianCylinder_isPullback R l h q' e H).isoPullback (by
    change (cartesianCylinder_isPullback R l h q' e H).isoPullback.hom ≫
      (pullback.fst U'.hom (polynomialProjection R) ≫ U'.hom) = T'.hom
    rw [← Category.assoc, IsPullback.isoPullback_hom_fst]
    exact MorphismProperty.Over.w q')

/-- The first projection is the supplied original-base map. -/
theorem cartesianCylinderIso_projection :
    (cartesianCylinderIso R l h q' e H).hom ≫ a1Projection R U' = q' := by
  apply MorphismProperty.Over.Hom.ext
  exact (cartesianCylinder_isPullback R l h q' e H).isoPullback_hom_fst

/-- The second projection is the unchanged coordinate from the original cylinder. -/
theorem cartesianCylinderIso_coordinate :
    (cartesianCylinderIso R l h q' e H).hom.left ≫
      pullback.snd U'.hom (polynomialProjection R) =
        h.left ≫ e.hom.left ≫ pullback.snd U.hom (polynomialProjection R) :=
  (cartesianCylinder_isPullback R l h q' e H).isoPullback_hom_snd

/-- The comparison retains the literal map into the original cylinder. -/
theorem cartesianCylinderIso_comp :
    (cartesianCylinderIso R l h q' e H).hom ≫ a1Map R l = h ≫ e.hom := by
  apply product_hom_ext
  · change ((cartesianCylinderIso R l h q' e H).hom ≫ a1Map R l) ≫
      a1Projection R U = (h ≫ e.hom) ≫ a1Projection R U
    calc
      _ = (cartesianCylinderIso R l h q' e H).hom ≫
          (a1Projection R U' ≫ l) := by rw [Category.assoc, a1Map_projection]
      _ = q' ≫ l := by rw [← Category.assoc, cartesianCylinderIso_projection]
      _ = (h ≫ e.hom) ≫ a1Projection R U := by
        apply MorphismProperty.Over.Hom.ext
        exact H.w.symm
  · simp only [a1Map, Category.assoc, productMap_snd, Category.comp_id]
    apply MorphismProperty.Over.Hom.ext
    exact cartesianCylinderIso_coordinate R l h q' e H

/-- Both supplied projections characterize the comparison map uniquely. -/
theorem cartesianCylinderIso_hom_unique (f : T' ⟶ a1Cylinder R U')
    (hf : f ≫ a1Projection R U' = q')
    (hf' : f.left ≫ pullback.snd U'.hom (polynomialProjection R) =
      h.left ≫ e.hom.left ≫ pullback.snd U.hom (polynomialProjection R)) :
    f = (cartesianCylinderIso R l h q' e H).hom := by
  apply product_hom_ext
  · exact hf.trans (cartesianCylinderIso_projection R l h q' e H).symm
  · apply MorphismProperty.Over.Hom.ext
    exact hf'.trans (cartesianCylinderIso_coordinate R l h q' e H).symm

end AlgebraicGeometry.Scheme.SmoothSite
