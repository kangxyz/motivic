/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.DerivedCategory.ImageResolutionHomology
public import Motivic.Aglib.Algebra.Homology.DerivedCategory.ConeHomologyWindow

/-! # Finite derived-functor vanishing for the actual image-resolution cone -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated HomologicalComplex
universe w v₁ v₂ u₁ u₂
namespace CategoryTheory.InjectiveResolution
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] [HasDerivedCategory.{w} D] {Y : C} (I : InjectiveResolution Y)
  (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R]

omit [PreservesFiniteLimits R] in
/-- The source of the actual image-resolution triangle has only degree-zero homology. -/
theorem imageTriangle_source_homology_zero (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor D i).obj (I.imageTriangle R).obj₁) :=
  (isZero_single_obj_homology (.up ℤ) 0 (R.obj Y) i hi).of_iso
    ((DerivedCategory.homologyFunctorFactors D i).app _)

/-- The actual augmentation induces an isomorphism in degree zero. -/
instance imageTriangle_homology_zero_isIso :
    IsIso ((DerivedCategory.homologyFunctor D 0).map (I.imageTriangle R).mor₁) := by
  change IsIso ((DerivedCategory.homologyFunctor D 0).map
    (DerivedCategory.Q.map (I.imageExtendedι R)))
  have h := DerivedCategory.homologyFunctorFactors_hom_naturality (I.imageExtendedι R) 0
  have he : (DerivedCategory.homologyFunctor D 0).map
      (DerivedCategory.Q.map (I.imageExtendedι R)) =
      (DerivedCategory.homologyFunctorFactors D 0).hom.app _ ≫
        homologyMap (I.imageExtendedι R) 0 ≫
          (DerivedCategory.homologyFunctorFactors D 0).inv.app _ := by
    rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id_app]
    erw [Category.comp_id]
  rw [he]
  infer_instance

/-- Every degree of the actual augmentation is monic on homology. -/
instance imageTriangle_homology_mono (i : ℤ) :
    Mono ((DerivedCategory.homologyFunctor D i).map (I.imageTriangle R).mor₁) := by
  by_cases hi : i = 0
  · subst i
    infer_instance
  · exact ⟨fun _ _ _ => (I.imageTriangle_source_homology_zero R i hi).eq_of_tgt _ _⟩

variable [HasInjectiveResolutions C]

omit [PreservesFiniteLimits R] [HasInjectiveResolutions C] in
/-- Negative image-resolution homology vanishes by actual extension by zero. -/
theorem imageTriangle_target_homology_negative (i : ℤ) (hi : i < 0) :
    IsZero ((DerivedCategory.homologyFunctor D i).obj (I.imageTriangle R).obj₂) := by
  apply ((I.imageComplex R).extend_exactAt ComplexShape.embeddingUpNat i
    (fun j => by change (j : ℤ) ≠ i; omega)).isZero_homology.of_iso
  exact (DerivedCategory.homologyFunctorFactors D i).app _

/-- Positive image-resolution homology is the genuine right-derived functor. -/
def imageTriangleTargetHomologyIso (n : ℕ) :
    (DerivedCategory.homologyFunctor D (n : ℤ)).obj (I.imageTriangle R).obj₂ ≅
      (R.rightDerived n).obj Y :=
  (DerivedCategory.homologyFunctorFactors D (n : ℤ)).app _ ≪≫
    I.imageExtendedHomologyIso R n

/-- The finite vanishing window kills the homology of the constructed cone. -/
theorem imageTriangle_cone_homology_zero (N : ℕ)
    (hR : ∀ q : ℕ, 0 < q → q ≤ N → IsZero ((R.rightDerived q).obj Y))
    (i : ℤ) (hi : i ≤ N) :
    IsZero ((DerivedCategory.homologyFunctor D i).obj (I.imageTriangle R).obj₃) := by
  have hepi : Epi ((DerivedCategory.homologyFunctor D i).map (I.imageTriangle R).mor₁) := by
    by_cases h0 : i = 0
    · subst i
      infer_instance
    · have hs := I.imageTriangle_source_homology_zero R i h0
      have ht : IsZero ((DerivedCategory.homologyFunctor D i).obj
          (I.imageTriangle R).obj₂) := by
        by_cases hn : i < 0
        · exact I.imageTriangle_target_homology_negative R i hn
        · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ i)
          exact (hR q (by omega) (by omega)).of_iso (I.imageTriangleTargetHomologyIso R q)
      have := hs.isIso ht ((DerivedCategory.homologyFunctor D i).map
        (I.imageTriangle R).mor₁)
      infer_instance
  exact DerivedCategory.cone_homology_isZero_of_epi_mono
    (I.imageTriangle R) (I.imageTriangle_distinguished R) i

/-- The actual image-resolution edge is bijective in the requested finite range. -/
theorem imageTriangle_postcomp_bijective (P : D) (N : ℕ)
    (hR : ∀ q : ℕ, 0 < q → q ≤ N → IsZero ((R.rightDerived q).obj Y)) :
    Function.Bijective (fun f : (DerivedCategory.singleFunctor D (N : ℤ)).obj P ⟶
      (I.imageTriangle R).obj₁ => f ≫ (I.imageTriangle R).mor₁) :=
  DerivedCategory.single_postcomp_bijective_of_cone_homology
    (I.imageTriangle R) (I.imageTriangle_distinguished R) P N
    (I.imageTriangle_cone_homology_zero R N hR)

/-- For injectivity the upper endpoint of the vanishing window is not required. -/
theorem imageTriangle_postcomp_injective (P : D) (N : ℕ)
    (hR : ∀ q : ℕ, 0 < q → q < N → IsZero ((R.rightDerived q).obj Y)) :
    Function.Injective (fun f : (DerivedCategory.singleFunctor D (N : ℤ)).obj P ⟶
      (I.imageTriangle R).obj₁ => f ≫ (I.imageTriangle R).mor₁) := by
  apply DerivedCategory.single_postcomp_injective_of_cone_homology
    (I.imageTriangle R) (I.imageTriangle_distinguished R) P N
  intro i hi
  exact I.imageTriangle_cone_homology_zero R (N - 1)
    (fun q hq hqN => hR q hq (by omega)) i (by omega)

end CategoryTheory.InjectiveResolution
