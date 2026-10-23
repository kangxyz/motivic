/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Nisnevich
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Products.ParameterProducts

/-! # Literal parameter products of small Nisnevich neighborhoods -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

variable {B : Scheme.{u}} (X T : SmoothSite B)

/-- The underlying smooth neighborhood maps to its original base. -/
def toBase (V : EtaleSeparatedFiniteType X.left) : (toSmoothSite X).obj V ⟶ X :=
  SmoothSite.homMk V.hom rfl

/-- Product of an étale neighborhood with the parameter is cartesian over its base. -/
theorem parameterProduct_isPullback (V : EtaleSeparatedFiniteType X.left) :
    IsPullback (SmoothSite.productMap (toBase X V) (𝟙 T)).left
      (SmoothSite.productFst ((toSmoothSite X).obj V) T).left
      (SmoothSite.productFst X T).left V.hom := by
  apply IsPullback.of_right (h₁₂ := (SmoothSite.productSnd X T).left)
    (h₂₂ := X.hom) (v₁₃ := T.hom)
  · change IsPullback
      ((SmoothSite.productMap (toBase X V) (𝟙 T)).left ≫ pullback.snd X.hom T.hom)
      (pullback.fst (V.hom ≫ X.hom) T.hom) T.hom (V.hom ≫ X.hom)
    have h := congrArg (fun f ↦ f.left) (SmoothSite.productMap_snd (toBase X V) (𝟙 T))
    change (SmoothSite.productMap (toBase X V) (𝟙 T)).left ≫
      pullback.snd X.hom T.hom = pullback.snd (V.hom ≫ X.hom) T.hom ≫ 𝟙 _ at h
    rw [h, Category.comp_id]
    exact (IsPullback.of_hasPullback _ _).flip
  · exact congrArg (fun f ↦ f.left) (SmoothSite.productMap_fst (toBase X V) (𝟙 T))
  · exact (IsPullback.of_hasPullback _ _).flip

instance parameterProduct_etale (V : EtaleSeparatedFiniteType X.left) :
    Etale (SmoothSite.productMap (toBase X V) (𝟙 T)).left :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @Etale) (parameterProduct_isPullback X T V).flip inferInstance

/-- Literal parameter products of finite-type étale neighborhoods. -/
def parameterProduct : EtaleSeparatedFiniteType X.left ⥤ EtaleSeparatedFiniteType
    (SmoothSite.product X T).left where
  obj V := MorphismProperty.Over.mk ⊤
    (SmoothSite.productMap (toBase X V) (𝟙 T)).left
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  map f := MorphismProperty.Over.homMk
    (SmoothSite.productMap ((toSmoothSite X).map f) (𝟙 T)).left (by
      change (SmoothSite.productMap ((toSmoothSite X).map f) (𝟙 T) ≫
        SmoothSite.productMap (toBase X _) (𝟙 T)).left = _
      rw [← SmoothSite.productMap_comp, Category.id_comp]
      have h : (toSmoothSite X).map f ≫ toBase X _ = toBase X _ :=
        MorphismProperty.Over.Hom.ext (MorphismProperty.Over.w f)
      rw [h]
      rfl)
  map_id V := by
    apply MorphismProperty.Over.Hom.ext
    change (SmoothSite.productMap (𝟙 _) (𝟙 T)).left = _
    rw [SmoothSite.productMap_id]
    rfl
  map_comp f g := by
    apply MorphismProperty.Over.Hom.ext
    have h := SmoothSite.productMap_comp ((toSmoothSite X).map f)
      ((toSmoothSite X).map g) (𝟙 T) (𝟙 T)
    simpa using congrArg (fun a ↦ a.left) h

/-- Forgetting a neighborhood product gives the original literal smooth product. -/
def parameterProductUnderlyingIso :
    parameterProduct X T ⋙ toSmoothSite (SmoothSite.product X T) ≅
      toSmoothSite X ⋙ SmoothSite.parameterProduct T :=
  NatIso.ofComponents (fun V ↦ MorphismProperty.Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ _ = _
    rw [Category.id_comp]
    exact (MorphismProperty.Over.w (SmoothSite.productMap (toBase X V) (𝟙 T))).symm))
    (fun f ↦ by
      apply MorphismProperty.Over.Hom.ext
      change (SmoothSite.productMap ((toSmoothSite X).map f) (𝟙 T)).left ≫ 𝟙 _ =
        𝟙 _ ≫ (SmoothSite.productMap ((toSmoothSite X).map f) (𝟙 T)).left
      simp only [Category.comp_id, Category.id_comp])

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
