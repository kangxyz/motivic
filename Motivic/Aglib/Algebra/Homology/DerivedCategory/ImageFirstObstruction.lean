/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.DerivedCategory.FirstHomologyDetection
public import Motivic.Aglib.Algebra.Homology.DerivedCategory.ImageResolutionWindow

/-! # The actual first nonzero right-derived-image obstruction -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
universe w v₁ v₂ u₁ u₂
namespace CategoryTheory.InjectiveResolution
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] [HasDerivedCategory.{w} C]
  (R : D ⥤ C) [R.Additive] [PreservesFiniteLimits R]
  [HasInjectiveResolutions D] {Y : D} (I : InjectiveResolution Y)
  (P : C) (N : ℕ)

/-- A literal map from the original degree-N source to the actual image resolution
has an obstruction valued in the actual right-derived image, not in an abstract cone. -/
def imageFirstObstruction
    (f : (DerivedCategory.singleFunctor C (N : ℤ)).obj P ⟶ (I.imageTriangle R).obj₂) :
    P ⟶ (R.rightDerived N).obj Y :=
  (DerivedCategory.singleFunctorCompHomologyFunctorIso C (N : ℤ)).inv.app P ≫
    (DerivedCategory.homologyFunctor C (N : ℤ)).map f ≫
      (I.imageTriangle_target_homology_iso R N).hom

omit [PreservesFiniteLimits R] in
/-- The obstruction is natural in the original coefficient source. -/
theorem imageFirstObstruction_naturality {P' : C} (a : P' ⟶ P)
    (f : (DerivedCategory.singleFunctor C (N : ℤ)).obj P ⟶ (I.imageTriangle R).obj₂) :
    I.imageFirstObstruction R P' N ((DerivedCategory.singleFunctor C (N : ℤ)).map a ≫ f) =
      a ≫ I.imageFirstObstruction R P N f := by
  simp only [imageFirstObstruction, Functor.map_comp, ← Category.assoc]
  have h := (DerivedCategory.singleFunctorCompHomologyFunctorIso C (N : ℤ)).inv.naturality a
  dsimp only [Functor.id_map, Functor.comp_map] at h
  rw [← h]

/-- Under the lower positive vanishing window, zero obstruction is exactly lifting
through the actual augmentation. Surjectivity of the obstruction is not asserted. -/
theorem imageFirstObstruction_eq_zero_iff
    (hN : 0 < N)
    (hR : ∀ q : ℕ, 0 < q → q < N → IsZero ((R.rightDerived q).obj Y))
    (f : (DerivedCategory.singleFunctor C (N : ℤ)).obj P ⟶ (I.imageTriangle R).obj₂) :
    I.imageFirstObstruction R P N f = 0 ↔
      ∃ g : (DerivedCategory.singleFunctor C (N : ℤ)).obj P ⟶ (I.imageTriangle R).obj₁,
        g ≫ (I.imageTriangle R).mor₁ = f := by
  have : (I.imageTriangle R).obj₃.IsGE (N : ℤ) :=
    (DerivedCategory.isGE_iff _ _).mpr (fun i hi =>
      I.imageTriangle_cone_homology_zero R (N - 1)
        (fun q hq hqN => hR q hq (by omega)) i (by omega))
  constructor
  · intro hf
    have hH : (DerivedCategory.homologyFunctor C (N : ℤ)).map f = 0 := by
      apply (cancel_epi
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso C (N : ℤ)).inv.app P)).mp
      apply (cancel_mono (I.imageTriangle_target_homology_iso R N).hom).mp
      simpa only [imageFirstObstruction, Category.assoc,
        Limits.zero_comp, Limits.comp_zero] using hf
    apply (DerivedCategory.single_lift_iff_first_homology_obstruction_zero
      (I.imageTriangle R) (I.imageTriangle_distinguished R) P (N : ℤ) f).mpr
    rw [Functor.map_comp, hH, Limits.zero_comp]
  · rintro ⟨g, rfl⟩
    have hz := I.imageTriangle_source_homology_zero R (N : ℤ) (by omega)
    have hg := hz.eq_of_tgt ((DerivedCategory.homologyFunctor C (N : ℤ)).map g) 0
    simp only [imageFirstObstruction, Functor.map_comp, hg,
      Limits.zero_comp, Limits.comp_zero]

end CategoryTheory.InjectiveResolution
