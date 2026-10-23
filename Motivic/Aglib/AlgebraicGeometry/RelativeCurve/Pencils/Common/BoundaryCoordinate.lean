/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.Boundary
/-! # Exact whole-boundary agreement for arbitrary relative-curve pencils -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil
variable {S X Y A B Z C D : Scheme.{u}}
  (q : X ⟶ S) [IsSeparated q] (π : C ⟶ S) (a : A ⟶ X) [Flat a]
  (z : Z ⟶ X)
  (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
    Hom.idealModule (Hom.boundaryGraphTarget q z))
  (ha : Disjoint (Set.range a) (Set.range z)) (d : D ⟶ C)

include ha in
/-- The original target scalar constructs the fixed-source unit on the whole product boundary. -/
theorem exists_fixedProductBoundaryFrame :
    let I := pullback (pullback.snd (a ≫ q) π) d
    let W := pullback (a ≫ q) (z ≫ q)
    ∃ E : SheafOfModules.unit (I ⨿ W).ringCatSheaf ≅
        SheafOfModules.unit (I ⨿ W).ringCatSheaf,
      (Scheme.Modules.restrictFunctor (coprod.inl : I ⟶ I ⨿ W)).map E.hom = 𝟙 _ ∧
      (Scheme.Modules.restrictFunctor (coprod.inr : W ⟶ I ⨿ W)).map E.hom ≫
        (restrictUnitIso _).hom = (restrictUnitIso _).hom ≫
          Hom.unitEndomorphismPullback (Hom.boundaryProductMap q a z)
            (e.hom ≫ Hom.idealInclusion (Hom.boundaryGraphTarget q z)) := by
  have := Hom.relativeBoundaryFrame_scalar_isIso q a z e ha
  exact exists_coprod_unitAutomorphism _ _ (asIso
    (Hom.unitEndomorphismPullback (Hom.boundaryProductMap q a z)
      (e.hom ≫ Hom.idealInclusion (Hom.boundaryGraphTarget q z))))

/-- The chosen unit automorphism with identity infinity restriction and the specified zero-boundary
scalar. -/
def fixedProductBoundaryFrame := Classical.choose (exists_fixedProductBoundaryFrame q π a z e ha d)

lemma fixedProductBoundaryFrame_inl :
    Hom.unitEndomorphismPullback coprod.inl (fixedProductBoundaryFrame q π a z e ha d).hom =
      𝟙 _ := by
  apply Hom.unitEndomorphismPullback_eq_of_restrict
  dsimp only [fixedProductBoundaryFrame]
  rw [(Classical.choose_spec (exists_fixedProductBoundaryFrame q π a z e ha d)).1]
  simp only [Category.id_comp, Category.comp_id]

lemma fixedProductBoundaryFrame_inr :
    Hom.unitEndomorphismPullback coprod.inr (fixedProductBoundaryFrame q π a z e ha d).hom =
      Hom.unitEndomorphismPullback (Hom.boundaryProductMap q a z)
        (e.hom ≫ Hom.idealInclusion (Hom.boundaryGraphTarget q z)) :=
  Hom.unitEndomorphismPullback_eq_of_restrict _ _ _
    (Classical.choose_spec (exists_fixedProductBoundaryFrame q π a z e ha d)).2

variable [SmoothOfRelativeDimension 1 q] [IsSeparated π]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  (p : Y ⟶ X) [Flat p] (hq : j ≫ π = p ≫ q)
  (α : B ⟶ Y) (β : B ⟶ A) (h : α ≫ p = β ≫ a)
  (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 _) p z)
  (hd : Disjoint (Set.range j) (Set.range d))

/-- Actual source maps and the original canonical graph section force whole-boundary agreement.
No coordinate equality or homotopy endpoint is assumed. -/
theorem commonBoundary_coordinate_eq :
    Hom.unitEndomorphismPullback (commonBoundaryToLambda π j α s d)
      (Hom.relativeFullBoundaryCoordinate q π j p hq z s hs H e d hd) =
    Hom.unitEndomorphismPullback (commonBoundaryToPsi q π j p hq a α β h z s hs d)
      (fixedProductBoundaryFrame q π a z e ha d).hom := by
  apply Hom.unitEndomorphism_ext_coprod
  · simp only [Hom.unitEndomorphismPullback_comp, commonBoundaryToLambda,
      commonBoundaryToPsi, coprod.inl_map]
    rw [← Hom.unitEndomorphismPullback_comp, ← Hom.unitEndomorphismPullback_comp,
      Hom.relativeFullBoundaryCoordinate_inl, fixedProductBoundaryFrame_inl]
    simp [Hom.unitEndomorphismPullback]
  · simp only [Hom.unitEndomorphismPullback_comp, commonBoundaryToLambda,
      commonBoundaryToPsi, coprod.inr_map]
    rw [← Hom.unitEndomorphismPullback_comp, ← Hom.unitEndomorphismPullback_comp,
      Hom.relativeFullBoundaryCoordinate_inr, fixedProductBoundaryFrame_inr,
      Hom.unitEndomorphismPullback_comp, Hom.unitEndomorphismPullback_comp,
      commonZero_coordinate_eq]
end AlgebraicGeometry.Scheme.RelativeCurvePencil
