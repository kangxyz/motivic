/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.DerivedCategory.AdjunctionImageEdgeWindow
public import Motivic.Aglib.Algebra.Homology.DerivedCategory.AdjunctionImageEdgeSingle
public import Motivic.Aglib.CategoryTheory.Triangulated.ShiftMapWindow

/-! # Finite-window edge comparison in the original shifted-target convention -/
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
  [PreservesFiniteLimits L] [PreservesFiniteColimits L] [PreservesFiniteLimits R]
  [HasInjectiveResolutions D] (adj : L ⊣ R)
  {Y : D} (I : InjectiveResolution Y) (P : C) (N : ℕ)
include I

/-- The constructed cone comparison gives the exact-functor/counit map on degree-N sources. -/
theorem singleImageEdge_bijective
    (hR : ∀ q : ℕ, 0 < q → q ≤ N → IsZero ((R.rightDerived q).obj Y)) :
    Function.Bijective (fun x : (DerivedCategory.singleFunctor C (N : ℤ)).obj P ⟶
      (DerivedCategory.singleFunctor C 0).obj (R.obj Y) =>
        L.mapDerivedCategory.map x ≫ adj.imageEdgeCounit Y) := by
  have h := adj.derivedImageEdge_bijective I P N hR
  constructor
  · intro x y hxy
    apply h.1
    simpa only [adj.derivedImageEdge_eq] using
      congrArg (L.mapDerivedCategoryFactors.inv.app
        ((CochainComplex.singleFunctor C (N : ℤ)).obj P) ≫ ·) hxy
  · intro y
    obtain ⟨x, hx⟩ := h.2 (L.mapDerivedCategoryFactors.inv.app
      ((CochainComplex.singleFunctor C (N : ℤ)).obj P) ≫ y)
    refine ⟨x, ?_⟩
    rw [adj.derivedImageEdge_eq] at hx
    exact (cancel_epi _).mp hx

/-- The same finite-window comparison in the original target-shift convention. -/
theorem shiftedImageEdge_bijective
    (hR : ∀ q : ℕ, 0 < q → q ≤ N → IsZero ((R.rightDerived q).obj Y)) :
    Function.Bijective (fun x : (DerivedCategory.singleFunctor C 0).obj P ⟶
      ((DerivedCategory.singleFunctor C 0).obj (R.obj Y))⟦(N : ℤ)⟧ =>
        L.mapDerivedCategory.map x ≫
          (L.mapDerivedCategory.commShiftIso (N : ℤ)).hom.app
            ((DerivedCategory.singleFunctor C 0).obj (R.obj Y)) ≫
              (adj.imageEdgeCounit Y)⟦(N : ℤ)⟧') := by
  have h := L.mapDerivedCategory.map_postcomp_shift_bijective
    (adj.imageEdgeCounit Y) (N : ℤ) (adj.singleImageEdge_bijective I P N hR)
  exact L.mapDerivedCategory.map_postcomp_isoSource_bijective _
    (((DerivedCategory.singleFunctors C).shiftIso (N : ℤ) 0 N (add_zero _)).app P) h

end CategoryTheory.Adjunction
