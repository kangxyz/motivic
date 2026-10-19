/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Diagonal.AffineMiddleSupports

/-!
# Affine presentations of diagonal support
-/

@[expose] public noncomputable section


set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct Algebra.TensorProduct.MiddleDiagonal

universe u

namespace AlgebraicGeometry.Scheme.Products.MiddleDiagonal

variable (k A B C : Type u) [CommRing k] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]

/-- Every actual left adjacent closed support has a constructed quotient presentation. -/
theorem exists_leftSupportPresentation {T : Scheme.{u}} (i : T ⟶ leftProduct k A B)
    [IsClosedImmersion i] :
    ∃ I : Ideal (A ⊗[k] B), ∃ e : Spec (CommRingCat.of ((A ⊗[k] B) ⧸ I)) ≅ T,
      e.hom ≫ i = leftSupportMap k A B I := by
  have h : IsClosedImmersion (i ≫ (leftIso k A B).inv) := inferInstance
  obtain ⟨I, e, he⟩ := IsClosedImmersion.Spec_iff.mp h
  refine ⟨I, e.symm, ?_⟩
  apply (cancel_mono (leftIso k A B).inv).mp
  simp only [Iso.symm_hom, leftSupportMap, Category.assoc]
  rw [he, Iso.inv_hom_id_assoc]
  simp [leftIso]

/-- Every actual right adjacent closed support has a constructed quotient presentation. -/
theorem exists_rightSupportPresentation {T : Scheme.{u}} (i : T ⟶ rightProduct k B C)
    [IsClosedImmersion i] :
    ∃ J : Ideal (B ⊗[k] C), ∃ e : Spec (CommRingCat.of ((B ⊗[k] C) ⧸ J)) ≅ T,
      e.hom ≫ i = rightSupportMap k B C J := by
  have h : IsClosedImmersion (i ≫ (rightIso k B C).inv) := inferInstance
  obtain ⟨J, e, he⟩ := IsClosedImmersion.Spec_iff.mp h
  refine ⟨J, e.symm, ?_⟩
  apply (cancel_mono (rightIso k B C).inv).mp
  simp only [Iso.symm_hom, rightSupportMap, Category.assoc]
  rw [he, Iso.inv_hom_id_assoc]
  simp [rightIso]


end AlgebraicGeometry.Scheme.Products.MiddleDiagonal
