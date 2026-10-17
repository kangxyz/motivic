/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.DerivedCategory.ImageResolutionAdjunction
public import Motivic.Aglib.Algebra.Homology.DerivedCategory.ImageResolutionAugmentation

/-! # The actual finite-window adjunction edge in the derived category -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe w₁ w₂ v₁ v₂ u₁ u₂
namespace CategoryTheory.Adjunction
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L] (adj : L ⊣ R)
  {Y : D} (I : InjectiveResolution Y) (K : CochainComplex C ℤ)

/-- The original exact inverse-image map followed by the original degreewise counit. -/
def derivedImageEdge (x : DerivedCategory.Q.obj K ⟶
    DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj (R.obj Y))) :
    DerivedCategory.Q.obj ((L.mapHomologicalComplex (.up ℤ)).obj K) ⟶
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor D 0).obj Y) :=
  L.mapDerivedCategoryFactors.inv.app K ≫ L.mapDerivedCategory.map x ≫
    L.mapDerivedCategoryFactors.hom.app _ ≫
      DerivedCategory.Q.map
        ((L.mapHomologicalComplex (.up ℤ)).map
          ((singleMapHomologicalComplex R (.up ℤ) 0).inv.app Y) ≫
            (NatTrans.mapHomologicalComplex adj.counit (.up ℤ)).app _)

/-- The actual resolution comparison is identified with its exact-functor and counit formula. -/
theorem imageResolutionHomAddEquiv_eq
    (x : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj
      ((I.imageComplex R).extend ComplexShape.embeddingUpNat)) :
    adj.imageResolutionHomAddEquiv I K x =
      L.mapDerivedCategoryFactors.inv.app K ≫ L.mapDerivedCategory.map x ≫
        L.mapDerivedCategoryFactors.hom.app _ ≫
          DerivedCategory.Q.map
            ((L.mapHomologicalComplex (.up ℤ)).map
              (I.cocomplex.mapExtendIso R ComplexShape.embeddingUpNat).inv ≫
                (NatTrans.mapHomologicalComplex adj.counit (.up ℤ)).app _) := by
  have := adj.mapExtendedResolution_isKInjective I
  change adj.kInjectiveHomAddEquiv K _
    (𝟙 _ ≫ x ≫ DerivedCategory.Q.map
      (I.cocomplex.mapExtendIso R ComplexShape.embeddingUpNat).inv) = _
  rw [Category.id_comp, adj.kInjectiveHomAddEquiv_eq, Functor.map_comp,
    Category.assoc,
    L.mapDerivedCategoryFactors_hom_naturality_assoc]
  simp only [Functor.map_comp]

/-- The constructed cone edge agrees with the actual adjunction arrow after augmentation. -/
theorem imageResolutionHomAddEquiv_augmentation
    (x : DerivedCategory.Q.obj K ⟶
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj (R.obj Y))) :
    adj.imageResolutionHomAddEquiv I K (x ≫ DerivedCategory.Q.map (I.imageExtendedι R)) =
      adj.derivedImageEdge K x ≫ DerivedCategory.Q.map I.extendedι := by
  rw [adj.imageResolutionHomAddEquiv_eq, Functor.map_comp,
    Category.assoc,
    L.mapDerivedCategoryFactors_hom_naturality_assoc]
  dsimp only [derivedImageEdge]
  simp only [Category.assoc, ← Functor.map_comp]
  congr 3
  rw [← Functor.map_comp_assoc, I.imageExtendedι_mapExtendIso,
    Functor.map_comp, ← Functor.map_comp]
  congr 1
  rw [Functor.map_comp, Category.assoc]
  erw [(NatTrans.mapHomologicalComplex adj.counit (.up ℤ)).naturality I.extendedι]
  rfl

end CategoryTheory.Adjunction
