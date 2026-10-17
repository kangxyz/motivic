/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Motivic.AlgebraicGeometry.Cycles.IntegralImage

/-!
# Finiteness of the projection from an actual closed image

If a source is finite over the base, its scheme-theoretic image in a separated
locally finite-type base scheme remains finite over that base. The proof
uses actual finite point fibres and the local finite-image theorem, then
globalizes finiteness on the target. No flatness, normality or reducedness
of the source is assumed.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic

set_option backward.isDefEq.respectTransparency false in
/-- An actual scheme-theoretic image retains the finite base projection. -/
theorem isFinite_image_projection {W T X : Scheme.{u}} (f : W ⟶ T) (p : T ⟶ X)
    [IsFinite (f ≫ p)] [IsSeparated p] [LocallyOfFiniteType p] :
    IsFinite (f.imageι ≫ p) := by
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := @IsFinite.{u}) (f := f.imageι ≫ p)
  intro x
  exact exists_finite_imageι_comp_morphismRestrict_of_finite_image_preimage f p x
    (((f ≫ p).finite_preimage_singleton x).image f)

/-- The image projection has exactly the original source image. This transfers
component dominance but does not prove it from whole-incidence coverage. -/
theorem range_image_projection {W T X : Scheme.{u}} (f : W ⟶ T) (p : T ⟶ X)
    [IsFinite f] : Set.range (f.imageι ≫ p) = Set.range (f ≫ p) := by
  have : Surjective f.toImage := ⟨surjective_toImage f⟩
  exact (range_eq_range_of_surjective (f ≫ p) (f.imageι ≫ p) f.toImage (by simp)).symm

end Motivic
