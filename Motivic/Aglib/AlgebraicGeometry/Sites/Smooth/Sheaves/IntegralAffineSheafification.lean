/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Sheaves.IntegralAffineSheafIso

/-! # Sheafifying maps specified on genuine integral affine sources -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite

universe u
namespace AlgebraicGeometry.Scheme.SmoothSite
variable (k : Type u) [Field k]

/-- Sheafification of a natural map given on the actual dense integral affine subsite. -/
def integralAffineSheafifyMap
    {F G : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}}
    (α : (integralAffineInclusion k).op ⋙ F ⟶ (integralAffineInclusion k).op ⋙ G) :
    (presheafToSheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).obj F ⟶
      (presheafToSheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).obj G :=
  ⟨sheafifyLift _ (extendIntegralAffineHom k
    (G := (presheafToSheaf (nisnevichTopology (Spec (.of k)))
      AddCommGrpCat.{u + 1}).obj G)
    (α ≫ whiskerLeft (integralAffineInclusion k).op
      (toSheafify (nisnevichTopology (Spec (.of k))) G)))
    ((presheafToSheaf (nisnevichTopology (Spec (.of k)))
      AddCommGrpCat.{u + 1}).obj G).property⟩

/-- Restricting the universal sheafified map recovers its original affine formula. -/
theorem integralAffineSheafifyMap_restrict
    {F G : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}}
    (α : (integralAffineInclusion k).op ⋙ F ⟶ (integralAffineInclusion k).op ⋙ G) :
    whiskerLeft (integralAffineInclusion k).op
      (toSheafify (nisnevichTopology (Spec (.of k))) F ≫
        (integralAffineSheafifyMap k α).hom) =
      α ≫ whiskerLeft (integralAffineInclusion k).op
        (toSheafify (nisnevichTopology (Spec (.of k))) G) := by
  dsimp only [integralAffineSheafifyMap]
  rw [toSheafify_sheafifyLift]
  exact Functor.IsCoverDense.sheafHom_restrict_eq _

/-- Maps between the original sheafifications are determined on affine raw sections. -/
theorem integralAffineSheafify_hom_ext
    {F G : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}}
    {a b : (presheafToSheaf (nisnevichTopology (Spec (.of k)))
      AddCommGrpCat.{u + 1}).obj F ⟶
      (presheafToSheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).obj G}
    (h : whiskerLeft (integralAffineInclusion k).op
      (toSheafify (nisnevichTopology (Spec (.of k))) F ≫ a.hom) =
      whiskerLeft (integralAffineInclusion k).op
        (toSheafify (nisnevichTopology (Spec (.of k))) F ≫ b.hom)) : a = b := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _
    ((presheafToSheaf (nisnevichTopology (Spec (.of k)))
      AddCommGrpCat.{u + 1}).obj G).property
  exact (Functor.IsCoverDense.restrictHomEquivHom
    (G := integralAffineInclusion k)
    (ℱ' := (presheafToSheaf (nisnevichTopology (Spec (.of k)))
      AddCommGrpCat.{u + 1}).obj G)).symm.injective h

/-- Composition is retained by the genuine dense-subsite sheafification map. -/
theorem integralAffineSheafifyMap_comp
    {F G H : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}}
    (α : (integralAffineInclusion k).op ⋙ F ⟶ (integralAffineInclusion k).op ⋙ G)
    (β : (integralAffineInclusion k).op ⋙ G ⟶ (integralAffineInclusion k).op ⋙ H) :
    integralAffineSheafifyMap k (α ≫ β) =
      integralAffineSheafifyMap k α ≫ integralAffineSheafifyMap k β := by
  apply integralAffineSheafify_hom_ext k
  rw [integralAffineSheafifyMap_restrict]
  change _ = whiskerLeft _ (_ ≫ (_ ≫ _))
  rw [← Category.assoc, whiskerLeft_comp, integralAffineSheafifyMap_restrict,
    Category.assoc]
  simp only [Category.assoc]
  rw [← whiskerLeft_comp, integralAffineSheafifyMap_restrict]

/-- Identity maps are retained without assuming the raw presheaves are sheaves. -/
theorem integralAffineSheafifyMap_id
    (F : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    integralAffineSheafifyMap k (𝟙 ((integralAffineInclusion k).op ⋙ F)) = 𝟙 _ := by
  apply integralAffineSheafify_hom_ext k
  rw [integralAffineSheafifyMap_restrict]
  simp

/-- An isomorphism on the dense integral affine subsite induces an isomorphism
of the original ordinary Nisnevich sheafifications. -/
def integralAffineSheafifyIso
    {F G : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}}
    (e : (integralAffineInclusion k).op ⋙ F ≅ (integralAffineInclusion k).op ⋙ G) :
    (presheafToSheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).obj F ≅
      (presheafToSheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).obj G where
  hom := integralAffineSheafifyMap k e.hom
  inv := integralAffineSheafifyMap k e.inv
  hom_inv_id := by rw [← integralAffineSheafifyMap_comp, e.hom_inv_id,
    integralAffineSheafifyMap_id]
  inv_hom_id := by rw [← integralAffineSheafifyMap_comp, e.inv_hom_id,
    integralAffineSheafifyMap_id]

/-- A genuine global presheaf map gives exactly the native sheafification map. -/
theorem integralAffineSheafifyMap_whisker
    {F G : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (f : F ⟶ G) :
    integralAffineSheafifyMap k (whiskerLeft (integralAffineInclusion k).op f) =
      (presheafToSheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).map f := by
  apply integralAffineSheafify_hom_ext k
  rw [integralAffineSheafifyMap_restrict, ← whiskerLeft_comp]
  exact congrArg (whiskerLeft (integralAffineInclusion k).op)
    (toSheafify_naturality (nisnevichTopology (Spec (.of k))) f)

/-- Surjectivity on actual integral affine sections suffices after Nisnevich sheafification. -/
theorem epi_sheafifyMap_of_integral_affine_surjective
    {F G : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (f : F ⟶ G)
    (h : ∀ (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left],
      Function.Surjective (f.app (op X))) :
    Epi ((presheafToSheaf (nisnevichTopology (Spec (.of k)))
      AddCommGrpCat.{u + 1}).map f) := by
  have hs : Presheaf.IsLocallySurjective (nisnevichTopology (Spec (.of k))) f := by
    constructor
    intro X x
    apply sieve_mem_of_integral_affine_arrows k
    intro U _ _ g
    exact h U (G.map g.op x)
  have := (Presheaf.isLocallySurjective_presheafToSheaf_map_iff
    (nisnevichTopology (Spec (.of k))) f).mpr hs
  infer_instance

end AlgebraicGeometry.Scheme.SmoothSite
