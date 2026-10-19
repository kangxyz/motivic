/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
/-! # Exact sections on both components of an original boundary coproduct

The native coproduct presheaf isomorphism detects equality on the full schemes,
including their nilpotents. No supportwise equality or reducedness is used.

Intended upstream module:
`Aglib.AlgebraicGeometry.Scheme.Sections.CoproductBoundary`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`Correction.NormalizedUnit`, `Norm.SectionPairNormNeighborhood`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme

/-- A section on an actual coproduct is determined by its two pullbacks. -/
theorem section_eq_of_coprod_app_eq {B₁ B₂ : Scheme.{u}}
    (W : (B₁ ⨿ B₂).Opens) (s t : Γ(B₁ ⨿ B₂, W))
    (h₁ : (coprod.inl : B₁ ⟶ B₁ ⨿ B₂).app W s =
      (coprod.inl : B₁ ⟶ B₁ ⨿ B₂).app W t)
    (h₂ : (coprod.inr : B₂ ⟶ B₁ ⨿ B₂).app W s =
      (coprod.inr : B₂ ⟶ B₁ ⨿ B₂).app W t) : s = t := by
  apply (coprodPresheafObjIso W).commRingCatIsoToRingEquiv.injective
  apply (Concrete.prodEquiv _ _).injective
  apply Prod.ext
  · simp only [Concrete.prodEquiv_apply_fst]
    change ((coprodPresheafObjIso W).hom ≫ prod.fst) s =
      ((coprodPresheafObjIso W).hom ≫ prod.fst) t
    rw [coprodPresheafObjIso_hom_fst]
    exact h₁
  · simp only [Concrete.prodEquiv_apply_snd]
    change ((coprodPresheafObjIso W).hom ≫ prod.snd) s =
      ((coprodPresheafObjIso W).hom ≫ prod.snd) t
    rw [coprodPresheafObjIso_hom_snd]
    exact h₂

/-- Literal value one on both boundary schemes gives value one on their entire
coproduct, over any target open. -/
theorem coprod_desc_app_eq_one {B₁ B₂ T : Scheme.{u}}
    (b₁ : B₁ ⟶ T) (b₂ : B₂ ⟶ T) (U : T.Opens) (μ : Γ(T, U))
    (h₁ : b₁.app U μ = 1) (h₂ : b₂.app U μ = 1) :
    (coprod.desc b₁ b₂).app U μ = 1 := by
  apply section_eq_of_coprod_app_eq
  · simp only [map_one, ← CommRingCat.comp_apply, ← Hom.comp_app]
    change (coprod.inl ≫ coprod.desc b₁ b₂).app U μ =
      (1 : Γ(B₁, (coprod.inl ≫ coprod.desc b₁ b₂) ⁻¹ᵁ U))
    exact (congrArg (fun g : B₁ ⟶ T => g.app U μ = 1)
      (coprod.inl_desc b₁ b₂)).mpr h₁
  · simp only [map_one, ← CommRingCat.comp_apply, ← Hom.comp_app]
    change (coprod.inr ≫ coprod.desc b₁ b₂).app U μ =
      (1 : Γ(B₂, (coprod.inr ≫ coprod.desc b₁ b₂) ⁻¹ᵁ U))
    exact (congrArg (fun g : B₂ ⟶ T => g.app U μ = 1)
      (coprod.inr_desc b₁ b₂)).mpr h₂

end AlgebraicGeometry.Scheme
