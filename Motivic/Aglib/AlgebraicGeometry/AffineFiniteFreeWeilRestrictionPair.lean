/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.AffineFiniteFreeWeilRestriction

/-!
# A common original affine-base refinement for two scalar witnesses

Two actual affine étale scalar witnesses over the same original affine base
produce one étale refinement by taking the product of their constructed Weil
restrictions. The same whole marking and both actual scalar evaluations are
retained. No general site-cofinality theorem is assumed or asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open Module

universe u

namespace AlgebraicGeometry.AffineWeilRestriction

variable {A B₁ B₂ C₁ C₂ : Type u}
variable [CommRing A] [CommRing B₁] [CommRing B₂] [CommRing C₁] [CommRing C₂]
variable [Algebra A B₁] [Algebra A B₂] [Algebra B₁ C₁] [Algebra B₂ C₂]
variable [Algebra.Etale B₁ C₁] [Algebra.Etale B₂ C₂]
variable {κ₁ κ₂ : Type u} [Fintype κ₁] [Fintype κ₂]
variable (b₁ : Basis κ₁ A B₁) (b₂ : Basis κ₂ A B₂)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The common refinement is the actual product over the original affine ambient scheme. -/
abbrev pairScheme : Scheme.{u} :=
  pullback (projection (C := C₁) b₁) (projection (C := C₂) b₂)

instance : IsAffine (pairScheme (C₁ := C₁) (C₂ := C₂) b₁ b₂) := inferInstance

/-- The original ambient arrow of the common refinement. -/
abbrev pairProjection : pairScheme (C₁ := C₁) (C₂ := C₂) b₁ b₂ ⟶ Spec (.of A) :=
  pullback.fst _ _ ≫ projection (C := C₁) b₁

instance : Etale (pairProjection (C₁ := C₁) (C₂ := C₂) b₁ b₂) := inferInstance

/-- Either factor gives the same original ambient arrow. -/
theorem pairProjection_eq_snd :
    pairProjection (C₁ := C₁) (C₂ := C₂) b₁ b₂ =
      pullback.snd _ _ ≫ projection (C := C₂) b₂ := pullback.condition

variable {T : Type u} [CommRing T] [Algebra A T]
variable (g₁ : C₁ →ₐ[B₁] T ⊗[A] B₁) (g₂ : C₂ →ₐ[B₂] T ⊗[A] B₂)

/-- A single lift of the whole original marking to the common product. -/
def pairMark : Spec (.of T) ⟶ pairScheme (C₁ := C₁) (C₂ := C₂) b₁ b₂ :=
  pullback.lift (mark b₁ g₁) (mark b₂ g₂)
    ((mark_over b₁ g₁).trans (mark_over b₂ g₂).symm)

@[reassoc (attr := simp)]
theorem pairMark_fst : pairMark b₁ b₂ g₁ g₂ ≫ pullback.fst _ _ = mark b₁ g₁ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem pairMark_snd : pairMark b₁ b₂ g₁ g₂ ≫ pullback.snd _ _ = mark b₂ g₂ :=
  pullback.lift_snd _ _ _

/-- The common whole marking remains over the unchanged original ambient base. -/
theorem pairMark_over : pairMark b₁ b₂ g₁ g₂ ≫ pairProjection b₁ b₂ =
    Spec.algebraMap A T := by
  rw [pairProjection, pairMark_fst_assoc, mark_over]

variable (S : Type u) [CommRing S] [Algebra A S]

/-- The actual base change of the common product's first projection. -/
def pairScalarFst :
    pullback (pairProjection (C₁ := C₁) (C₂ := C₂) b₁ b₂) (Spec.algebraMap A S) ⟶
      pullback (projection (C := C₁) b₁) (Spec.algebraMap A S) :=
  pullback.map _ _ _ _ (pullback.fst _ _) (𝟙 _) (𝟙 _) (by simp) (by simp)

/-- The actual base change of the common product's second projection. -/
def pairScalarSnd :
    pullback (pairProjection (C₁ := C₁) (C₂ := C₂) b₁ b₂) (Spec.algebraMap A S) ⟶
      pullback (projection (C := C₂) b₂) (Spec.algebraMap A S) :=
  pullback.map _ _ _ _ (pullback.snd _ _) (𝟙 _) (𝟙 _)
    (by simpa using pairProjection_eq_snd (C₁ := C₁) (C₂ := C₂) b₁ b₂) (by simp)

/-- The scalar extension of the single whole original marking. -/
def pairScalarMark :
    pullback (Spec.algebraMap A T) (Spec.algebraMap A S) ⟶
      pullback (pairProjection (C₁ := C₁) (C₂ := C₂) b₁ b₂) (Spec.algebraMap A S) :=
  pullback.map _ _ _ _ (pairMark b₁ b₂ g₁ g₂) (𝟙 _) (𝟙 _)
    (by simpa using (pairMark_over b₁ b₂ g₁ g₂).symm) (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- The first scalar projection recovers the original whole first marking. -/
theorem pairScalarMark_fst :
    pairScalarMark b₁ b₂ g₁ g₂ B₁ ≫ pairScalarFst (C₁ := C₁) (C₂ := C₂) b₁ b₂ B₁ =
      scalarMark b₁ g₁ := by
  apply pullback.hom_ext
  · simp [pairScalarMark, pairScalarFst, pullback.map, Category.assoc, scalarMark_fst]
  · simp [pairScalarMark, pairScalarFst, pullback.map, Category.assoc, scalarMark_snd]

set_option backward.isDefEq.respectTransparency false in
/-- The second scalar projection recovers the original whole second marking. -/
theorem pairScalarMark_snd :
    pairScalarMark b₁ b₂ g₁ g₂ B₂ ≫ pairScalarSnd (C₁ := C₁) (C₂ := C₂) b₁ b₂ B₂ =
      scalarMark b₂ g₂ := by
  apply pullback.hom_ext
  · simp [pairScalarMark, pairScalarSnd, pullback.map, Category.assoc, scalarMark_fst]
  · simp [pairScalarMark, pairScalarSnd, pullback.map, Category.assoc, scalarMark_snd]

/-- The first actual scalar evaluation from the common original refinement. -/
def pairEvaluationLeft :
    pullback (pairProjection (C₁ := C₁) (C₂ := C₂) b₁ b₂) (Spec.algebraMap A B₁) ⟶
      Spec (.of C₁) :=
  pairScalarFst (C₁ := C₁) (C₂ := C₂) b₁ b₂ B₁ ≫ scalarEvaluation b₁

/-- The second actual scalar evaluation from the common original refinement. -/
def pairEvaluationRight :
    pullback (pairProjection (C₁ := C₁) (C₂ := C₂) b₁ b₂) (Spec.algebraMap A B₂) ⟶
      Spec (.of C₂) :=
  pairScalarSnd (C₁ := C₁) (C₂ := C₂) b₁ b₂ B₂ ≫ scalarEvaluation b₂

set_option backward.isDefEq.respectTransparency false in
/-- The first evaluation is over the first actual scalar ambient base. -/
theorem pairEvaluationLeft_over :
    pairEvaluationLeft (C₁ := C₁) (C₂ := C₂) b₁ b₂ ≫ Spec.algebraMap B₁ C₁ =
      pullback.snd (pairProjection (C₁ := C₁) (C₂ := C₂) b₁ b₂)
        (Spec.algebraMap A B₁) := by
  rw [pairEvaluationLeft, Category.assoc, scalarEvaluation_over]
  simp [pairScalarFst, pullback.map]

set_option backward.isDefEq.respectTransparency false in
/-- The second evaluation is over the second actual scalar ambient base. -/
theorem pairEvaluationRight_over :
    pairEvaluationRight (C₁ := C₁) (C₂ := C₂) b₁ b₂ ≫ Spec.algebraMap B₂ C₂ =
      pullback.snd (pairProjection (C₁ := C₁) (C₂ := C₂) b₁ b₂)
        (Spec.algebraMap A B₂) := by
  rw [pairEvaluationRight, Category.assoc, scalarEvaluation_over]
  simp [pairScalarSnd, pullback.map]

/-- The first evaluation agrees with the entire prescribed scalar marking. -/
theorem pairEvaluationLeft_mark :
    pairScalarMark b₁ b₂ g₁ g₂ B₁ ≫ pairEvaluationLeft b₁ b₂ =
      (pullbackSpecIso A T B₁).hom ≫ Spec.map (CommRingCat.ofHom g₁.toRingHom) := by
  rw [pairEvaluationLeft, ← Category.assoc, pairScalarMark_fst, scalarMark_evaluation]

/-- The second evaluation agrees with the entire prescribed scalar marking. -/
theorem pairEvaluationRight_mark :
    pairScalarMark b₁ b₂ g₁ g₂ B₂ ≫ pairEvaluationRight b₁ b₂ =
      (pullbackSpecIso A T B₂).hom ≫ Spec.map (CommRingCat.ofHom g₂.toRingHom) := by
  rw [pairEvaluationRight, ← Category.assoc, pairScalarMark_snd, scalarMark_evaluation]

end AlgebraicGeometry.AffineWeilRestriction
