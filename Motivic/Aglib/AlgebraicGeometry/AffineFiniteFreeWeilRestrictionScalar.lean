/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.AffineFiniteFreeWeilRestrictionPair
public import Motivic.Aglib.AlgebraicGeometry.AffineScalarPullback

/-!
# Actual Weil-pair evaluation on original scalar extensions

Both extension algebras are literal tensor products over the ground ring.
Evaluation starts at scalar extension of the original product scheme, not at
an unrelated abstract scalar object. Both original ambient and scalar-base
projections are retained.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open Module

universe u

namespace AlgebraicGeometry.AffineWeilRestriction

variable {R A L₁ L₂ C₁ C₂ : Type u}
variable [CommRing R] [CommRing A] [CommRing L₁] [CommRing L₂]
variable [CommRing C₁] [CommRing C₂]
variable [Algebra R A] [Algebra R L₁] [Algebra R L₂]
variable [Algebra (A ⊗[R] L₁) C₁] [Algebra (A ⊗[R] L₂) C₂]
variable [Algebra.Etale (A ⊗[R] L₁) C₁] [Algebra.Etale (A ⊗[R] L₂) C₂]
variable {κ₁ κ₂ : Type u} [Fintype κ₁] [Fintype κ₂]
variable (b₁ : Basis κ₁ R L₁) (b₂ : Basis κ₂ R L₂)

/-- The first evaluation on the literal original scalar extension. -/
def pairNativeEvaluationLeft :
    pullback (pairProjection (C₁ := C₁) (C₂ := C₂)
      (b₁.baseChange A) (b₂.baseChange A) ≫ Spec.algebraMap R A)
      (Spec.algebraMap R L₁) ⟶ Spec (.of C₁) :=
  (affineScalarPullbackIso R A L₁
    (pairProjection (C₁ := C₁) (C₂ := C₂) (b₁.baseChange A) (b₂.baseChange A))).hom ≫
      pairEvaluationLeft (b₁.baseChange A) (b₂.baseChange A)

/-- The second evaluation on the same original product's literal scalar extension. -/
def pairNativeEvaluationRight :
    pullback (pairProjection (C₁ := C₁) (C₂ := C₂)
      (b₁.baseChange A) (b₂.baseChange A) ≫ Spec.algebraMap R A)
      (Spec.algebraMap R L₂) ⟶ Spec (.of C₂) :=
  (affineScalarPullbackIso R A L₂
    (pairProjection (C₁ := C₁) (C₂ := C₂) (b₁.baseChange A) (b₂.baseChange A))).hom ≫
      pairEvaluationRight (b₁.baseChange A) (b₂.baseChange A)

set_option backward.isDefEq.respectTransparency false in
/-- The first evaluation preserves the unchanged original ambient arrow. -/
@[reassoc]
theorem pairNativeEvaluationLeft_ambient :
    pairNativeEvaluationLeft (A := A) (C₁ := C₁) (C₂ := C₂) b₁ b₂ ≫
        Spec.algebraMap (A ⊗[R] L₁) C₁ ≫ Spec.algebraMap A (A ⊗[R] L₁) =
      pullback.fst _ _ ≫ pairProjection (C₁ := C₁) (C₂ := C₂)
        (b₁.baseChange A) (b₂.baseChange A) := by
  simp only [pairNativeEvaluationLeft, Category.assoc,
    reassoc_of% (pairEvaluationLeft_over (C₁ := C₁) (C₂ := C₂)
      (b₁.baseChange A) (b₂.baseChange A))]
  rw [← pullback.condition (f := pairProjection (C₁ := C₁) (C₂ := C₂)
    (b₁.baseChange A) (b₂.baseChange A)) (g := Spec.algebraMap A (A ⊗[R] L₁))]
  exact affineScalarPullbackIso_hom_fst_assoc R A L₁ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The second evaluation preserves the same unchanged original ambient arrow. -/
@[reassoc]
theorem pairNativeEvaluationRight_ambient :
    pairNativeEvaluationRight (A := A) (C₁ := C₁) (C₂ := C₂) b₁ b₂ ≫
        Spec.algebraMap (A ⊗[R] L₂) C₂ ≫ Spec.algebraMap A (A ⊗[R] L₂) =
      pullback.fst _ _ ≫ pairProjection (C₁ := C₁) (C₂ := C₂)
        (b₁.baseChange A) (b₂.baseChange A) := by
  simp only [pairNativeEvaluationRight, Category.assoc,
    reassoc_of% (pairEvaluationRight_over (C₁ := C₁) (C₂ := C₂)
      (b₁.baseChange A) (b₂.baseChange A))]
  rw [← pullback.condition (f := pairProjection (C₁ := C₁) (C₂ := C₂)
    (b₁.baseChange A) (b₂.baseChange A)) (g := Spec.algebraMap A (A ⊗[R] L₂))]
  exact affineScalarPullbackIso_hom_fst_assoc R A L₂ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The first evaluation retains the original scalar-base projection. -/
@[reassoc]
theorem pairNativeEvaluationLeft_scalar :
    pairNativeEvaluationLeft (A := A) (C₁ := C₁) (C₂ := C₂) b₁ b₂ ≫
        Spec.algebraMap (A ⊗[R] L₁) C₁ ≫ Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := L₁)).toRingHom) =
      pullback.snd _ _ := by
  simp only [pairNativeEvaluationLeft, Category.assoc,
    reassoc_of% (pairEvaluationLeft_over (C₁ := C₁) (C₂ := C₂)
      (b₁.baseChange A) (b₂.baseChange A))]
  exact affineScalarPullbackIso_hom_scalar R A L₁ _

set_option backward.isDefEq.respectTransparency false in
/-- The second evaluation retains its own original scalar-base projection. -/
@[reassoc]
theorem pairNativeEvaluationRight_scalar :
    pairNativeEvaluationRight (A := A) (C₁ := C₁) (C₂ := C₂) b₁ b₂ ≫
        Spec.algebraMap (A ⊗[R] L₂) C₂ ≫ Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := L₂)).toRingHom) =
      pullback.snd _ _ := by
  simp only [pairNativeEvaluationRight, Category.assoc,
    reassoc_of% (pairEvaluationRight_over (C₁ := C₁) (C₂ := C₂)
      (b₁.baseChange A) (b₂.baseChange A))]
  exact affineScalarPullbackIso_hom_scalar R A L₂ _

end AlgebraicGeometry.AffineWeilRestriction
