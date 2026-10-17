/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.DerivedCategory.AdjunctionImageEdge

/-! # Finite vanishing windows for the actual derived adjunction edge -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe w₁ w₂ v₁ v₂ u₁ u₂
namespace CategoryTheory.Adjunction
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L] [PreservesFiniteLimits R]
  [HasInjectiveResolutions D] (adj : L ⊣ R)
  {Y : D} (I : InjectiveResolution Y) (P : C) (N : ℕ)

include I

/-- A finite positive derived-image vanishing window gives injectivity of the actual edge. -/
theorem derivedImageEdge_injective
    (hR : ∀ q : ℕ, 0 < q → q < N → IsZero ((R.rightDerived q).obj Y)) :
    Function.Injective (adj.derivedImageEdge ((CochainComplex.singleFunctor C (N : ℤ)).obj P)
      (Y := Y)) := by
  intro x y h
  apply I.imageTriangle_postcomp_injective R P N hR
  apply (adj.imageResolutionHomAddEquiv I _).injective
  change adj.imageResolutionHomAddEquiv I _ (x ≫ DerivedCategory.Q.map (I.imageExtendedι R)) =
    adj.imageResolutionHomAddEquiv I _ (y ≫ DerivedCategory.Q.map (I.imageExtendedι R))
  rw [adj.imageResolutionHomAddEquiv_augmentation,
    adj.imageResolutionHomAddEquiv_augmentation, h]

/-- The endpoint-inclusive finite window gives bijectivity of that same actual edge. -/
theorem derivedImageEdge_bijective
    (hR : ∀ q : ℕ, 0 < q → q ≤ N → IsZero ((R.rightDerived q).obj Y)) :
    Function.Bijective (adj.derivedImageEdge ((CochainComplex.singleFunctor C (N : ℤ)).obj P)
      (Y := Y)) := by
  refine ⟨adj.derivedImageEdge_injective I P N (fun q hq hqN => hR q hq (by omega)), ?_⟩
  intro y
  let z := (adj.imageResolutionHomAddEquiv I _).symm (y ≫ DerivedCategory.Q.map I.extendedι)
  obtain ⟨x, hx⟩ := (I.imageTriangle_postcomp_bijective R P N hR).2 z
  refine ⟨x, ?_⟩
  apply (cancel_mono (DerivedCategory.Q.map I.extendedι)).mp
  erw [← adj.imageResolutionHomAddEquiv_augmentation]
  change adj.imageResolutionHomAddEquiv I _ (x ≫ (I.imageTriangle R).mor₁) = _
  dsimp only at hx
  erw [hx]
  exact (adj.imageResolutionHomAddEquiv I _).apply_symm_apply _

end CategoryTheory.Adjunction
