/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Compactification.Retained.PrescribedBoundary
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Retain the original prescribed nonreduced quotient inside the constructed bad scheme -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurve
variable (B : Type u) [CommRing B] (I J : Ideal B) (hIJ : I ≤ J)

/-- The actual original quotient is a closed subscheme of the constructed bad scheme. -/
def prescribedSubquotient : Spec (.of (B ⧸ J)) ⟶ Spec (.of (B ⧸ I)) :=
  Spec.map (CommRingCat.ofHom (Ideal.quotientMap J (RingHom.id B) (by simpa using hIJ)))

instance : IsClosedImmersion (prescribedSubquotient B I J hIJ) :=
  IsClosedImmersion.spec_of_surjective _
    (Ideal.quotientMap_surjective (H := by simpa using hIJ) Function.surjective_id)

@[reassoc (attr := simp)]
theorem prescribedSubquotient_comp : prescribedSubquotient B I J hIJ ≫
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
  rw [prescribedSubquotient, ← Spec.map_comp]
  congr 1

include hIJ

/-- Finiteness descends to the full original quotient, without taking its reduction. -/
theorem prescribedSubquotient_finite {S : Scheme.{u}} (f : Spec (.of B) ⟶ S)
    [IsFinite (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ f)] :
    IsFinite (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ f) := by
  rw [← prescribedSubquotient_comp B I J hIJ, Category.assoc]
  infer_instance

/-- The same base neighborhood retains every point of the original quotient. -/
theorem prescribedSubquotient_retained {N S : Scheme.{u}} (i : Spec (.of B) ⟶ N)
    (f : Spec (.of B) ⟶ S) (T : S.Opens) (V : N.Opens)
    (h : ∀ x : Spec (.of (B ⧸ I)),
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ f) x ∈ T →
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ i) x ∈ V) :
    ∀ x : Spec (.of (B ⧸ J)),
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ f) x ∈ T →
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ i) x ∈ V := by
  intro x hx
  have := h (prescribedSubquotient B I J hIJ x)
  simpa only [← Scheme.Hom.comp_apply, prescribedSubquotient_comp_assoc] using this hx

end AlgebraicGeometry.Scheme.RelativeCurve
