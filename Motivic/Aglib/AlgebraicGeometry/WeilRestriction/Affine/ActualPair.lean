/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.WeilRestriction.Affine.FiniteFree.Pair
public import Motivic.Aglib.AlgebraicGeometry.WeilRestriction.Affine.Witness

/-!
# A constructed common original refinement of actual affine scalar witnesses

The two input witnesses are actual affine schemes with actual étale arrows.
Their coordinate rings and algebra maps are derived using canonical isoSpec.
The output is the concrete Weil product over the unchanged original Spec A,
with the entire original mark and both scalar evaluation equations.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open Module

universe u

namespace AlgebraicGeometry.AffineWeilRestriction

variable {A B₁ B₂ T : Type u}
variable [CommRing A] [CommRing B₁] [CommRing B₂] [CommRing T]
variable [Algebra A B₁] [Algebra A B₂] [Algebra A T]
variable {κ₁ κ₂ : Type u} [Finite κ₁] [Finite κ₂]
variable (b₁ : Basis κ₁ A B₁) (b₂ : Basis κ₂ A B₂)
variable {E₁ E₂ : Scheme.{u}} [IsAffine E₁] [IsAffine E₂]
variable (f₁ : E₁ ⟶ Spec (.of B₁)) (f₂ : E₂ ⟶ Spec (.of B₂))
variable [Etale f₁] [Etale f₂]
variable (t₁ : pullback (Spec.algebraMap A T) (Spec.algebraMap A B₁) ⟶ E₁)
variable (t₂ : pullback (Spec.algebraMap A T) (Spec.algebraMap A B₂) ⟶ E₂)
variable (ht₁ : t₁ ≫ f₁ = pullback.snd (Spec.algebraMap A T) (Spec.algebraMap A B₁))
variable (ht₂ : t₂ ≫ f₂ = pullback.snd (Spec.algebraMap A T) (Spec.algebraMap A B₂))

include b₁ b₂ ht₁ ht₂ in
set_option backward.isDefEq.respectTransparency false in
/-- Actual affine étale scalar witnesses with the same whole original marking
admit a constructed common affine étale refinement over the original ambient. -/
theorem exists_affine_etale_pair_of_scalar_sections :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ Spec (.of A)) (z : Spec (.of T) ⟶ Y)
      (hz : z ≫ p = Spec.algebraMap A T),
      IsAffine Y ∧ Etale p ∧
      ∃ (e₁ : pullback p (Spec.algebraMap A B₁) ⟶ E₁)
        (e₂ : pullback p (Spec.algebraMap A B₂) ⟶ E₂),
        e₁ ≫ f₁ = pullback.snd p (Spec.algebraMap A B₁) ∧
        e₂ ≫ f₂ = pullback.snd p (Spec.algebraMap A B₂) ∧
        pullback.map (Spec.algebraMap A T) (Spec.algebraMap A B₁)
          p (Spec.algebraMap A B₁) z (𝟙 _) (𝟙 _)
          (by simpa using hz.symm) (by simp) ≫ e₁ = t₁ ∧
        pullback.map (Spec.algebraMap A T) (Spec.algebraMap A B₂)
          p (Spec.algebraMap A B₂) z (𝟙 _) (𝟙 _)
          (by simpa using hz.symm) (by simp) ≫ e₂ = t₂ := by
  let : Fintype κ₁ := Fintype.ofFinite κ₁
  let : Fintype κ₂ := Fintype.ofFinite κ₂
  let := witnessAlgebra f₁
  let := witnessAlgebra f₂
  let := witnessAlgebra_etale f₁
  let := witnessAlgebra_etale f₂
  let g₁ := witnessScalarMarkHom f₁ t₁ ht₁
  let g₂ := witnessScalarMarkHom f₂ t₂ ht₂
  let p := pairProjection (C₁ := Γ(E₁, ⊤)) (C₂ := Γ(E₂, ⊤)) b₁ b₂
  let z := pairMark b₁ b₂ g₁ g₂
  refine ⟨pairScheme b₁ b₂, p, z, pairMark_over b₁ b₂ g₁ g₂,
    inferInstance, inferInstance,
    pairEvaluationLeft b₁ b₂ ≫ E₁.isoSpec.inv,
    pairEvaluationRight b₁ b₂ ≫ E₂.isoSpec.inv, ?_, ?_, ?_, ?_⟩
  · rw [Category.assoc, ← witnessAlgebra_projection f₁, pairEvaluationLeft_over]
  · rw [Category.assoc, ← witnessAlgebra_projection f₂, pairEvaluationRight_over]
  · change pairScalarMark b₁ b₂ g₁ g₂ B₁ ≫
      (pairEvaluationLeft b₁ b₂ ≫ E₁.isoSpec.inv) = t₁
    rw [← Category.assoc, pairEvaluationLeft_mark]
    simpa only [Category.assoc] using witnessScalarMarkHom_spec f₁ t₁ ht₁
  · change pairScalarMark b₁ b₂ g₁ g₂ B₂ ≫
      (pairEvaluationRight b₁ b₂ ≫ E₂.isoSpec.inv) = t₂
    rw [← Category.assoc, pairEvaluationRight_mark]
    simpa only [Category.assoc] using witnessScalarMarkHom_spec f₂ t₂ ht₂

end AlgebraicGeometry.AffineWeilRestriction
