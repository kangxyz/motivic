/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.PresheavesWithTransfers.ContractionGeometry
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.Polynomial.Ideal

/-! # The actual zero section is the complement of the Laurent cylinder -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Motivic.SmoothSite

/-- The actual product in its second factor is a scheme-theoretic base change. -/
theorem productMap_right_isPullback {S : Scheme.{u}} (X : SmoothSite S)
    {U V : SmoothSite S} (j : U ⟶ V) :
    IsPullback (productMap (𝟙 X) j).left (productSnd X U).left
      (productSnd X V).left j.left := by
  apply IsPullback.of_right (h₁₂ := (productFst X V).left)
    (h₂₂ := V.hom) (v₁₃ := X.hom)
  · have hf := congrArg (fun f => f.left) (productMap_fst (𝟙 X) j)
    change (productMap (𝟙 X) j).left ≫ (productFst X V).left =
      (productFst X U).left ≫ 𝟙 X.left at hf
    rw [hf, Category.comp_id, MorphismProperty.Over.w]
    exact IsPullback.of_hasPullback X.hom U.hom
  · exact congrArg (fun f => f.left) (productMap_snd (𝟙 X) j)
  · exact IsPullback.of_hasPullback X.hom V.hom

variable (R : CommRingCat.{u}) (X : SmoothSite (Spec R))

/-- The relative constant section is the base change of the original field-independent point. -/
theorem a1Section_isPullback (a : R) :
    IsPullback (a1Section R X a).left X.hom
      (productSnd X (affineLine R)).left (affineLinePoint R a).left := by
  apply IsPullback.of_right (h₁₂ := (a1Projection R X).left)
    (h₂₂ := (affineLine R).hom) (v₁₃ := X.hom)
  · have hf := congrArg (fun f => f.left) (a1Section_projection R X a)
    change (a1Section R X a).left ≫ (a1Projection R X).left = 𝟙 X.left at hf
    rw [hf, MorphismProperty.Over.w]
    change IsPullback (𝟙 X.left) X.hom X.hom (𝟙 _)
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  · exact congrArg (fun f => f.left) (productLift_snd (𝟙 X)
      ((homMk X.hom (Category.comp_id _) : X ⟶ base (Spec R)) ≫ affineLinePoint R a))
  · exact IsPullback.of_hasPullback X.hom (affineLine R).hom

instance contractionOpen_isOpenImmersion : IsOpenImmersion (contractionOpen R X).left :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion)
    (productMap_right_isPullback X (torusInAffineLine R)).flip inferInstance

instance a1Section_isClosedImmersion (a : R) : IsClosedImmersion (a1Section R X a).left := by
  have : IsClosedImmersion (affineLinePoint R a).left :=
    IsClosedImmersion.spec_of_surjective _ (fun r => ⟨Polynomial.C r, by simp⟩)
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion)
    (a1Section_isPullback R X a).flip inferInstance

private theorem range_fst_of_isPullback {P A B C : Scheme.{u}}
    {a : P ⟶ A} {b : P ⟶ B} {f : A ⟶ C} {g : B ⟶ C}
    (h : IsPullback a b f g) : Set.range a = f ⁻¹' Set.range g := by
  rw [← h.isoPullback_hom_fst]
  change Set.range ((pullback.fst f g) ∘ h.isoPullback.hom) = _
  rw [Set.range_comp, Set.range_eq_univ.mpr h.isoPullback.hom.surjective,
    Set.image_univ, Scheme.Pullback.range_fst]

/-- The whole closed complement of the original Laurent cylinder is the literal zero section. -/
theorem range_a1Section_zero :
    Set.range (a1Section R X 0).left = (Set.range (contractionOpen R X).left)ᶜ := by
  change Set.range (a1Section R X 0).left =
    (Set.range (productMap (𝟙 X) (torusInAffineLine R)).left)ᶜ
  rw [range_fst_of_isPullback (a1Section_isPullback R X 0),
    range_fst_of_isPullback (productMap_right_isPullback X (torusInAffineLine R))]
  have hz : Set.range (affineLinePoint R 0).left =
      (Set.range (torusInAffineLine R).left)ᶜ := by
    change Set.range (PrimeSpectrum.comap (Polynomial.evalRingHom (0 : R))) =
      (Set.range (Scheme.PolynomialLaurent.laurentPlus R))ᶜ
    rw [range_comap_of_surjective _ _
      (fun x => ⟨Polynomial.C x, by simp⟩), Polynomial.ker_evalRingHom]
    rw [← Scheme.Hom.coe_opensRange, Scheme.PolynomialLaurent.laurentPlus_opensRange]
    simp only [Polynomial.C_0, sub_zero, PrimeSpectrum.zeroLocus_span]
    ext x
    simp only [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, Set.mem_compl_iff]
    change (Polynomial.X : Polynomial R) ∈ x.asIdeal ↔
      ¬ (Polynomial.X : Polynomial R) ∉ x.asIdeal
    exact not_not.symm
  exact congrArg (fun A : Set (affineLine R).left =>
    (productSnd X (affineLine R)).left ⁻¹' A) hz

end Motivic.SmoothSite
