/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.DerivedCategory.KInjectiveAdjunctionMap
public import Motivic.Aglib.Algebra.Homology.DerivedCategory.ImageResolutionWindow
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-! # K-injective targets of the actual adjoint image-resolution comparison -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe w₁ w₂ v₁ v₂ u₁ u₂
namespace CategoryTheory.Adjunction
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] (adj : L ⊣ R) {Y : D} (I : InjectiveResolution Y)

omit [L.Additive] in
include adj in
/-- Actual images of resolution terms are injective, using the original adjunction. -/
theorem imageResolution_term_injective (n : ℕ) : Injective ((I.imageComplex R).X n) :=
  Injective.injective_of_adjoint adj _

omit [L.Additive] in
include adj in
/-- The actual image resolution, extended by zero, is K-injective without acyclicity input. -/
theorem imageResolution_isKInjective :
    CochainComplex.IsKInjective ((I.imageComplex R).extend ComplexShape.embeddingUpNat) := by
  let (n : ℕ) : Injective ((I.imageComplex R).X n) := adj.imageResolution_term_injective I n
  infer_instance

include adj in
omit [L.Additive] in
/-- Applying the actual right adjoint to the extended resolution is also K-injective. -/
theorem mapExtendedResolution_isKInjective :
    CochainComplex.IsKInjective
      ((R.mapHomologicalComplex (.up ℤ)).obj (I.cocomplex.extend ComplexShape.embeddingUpNat)) := by
  let : CochainComplex.IsKInjective
      (((R.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extend
        ComplexShape.embeddingUpNat) :=
    adj.imageResolution_isKInjective I
  exact CochainComplex.isKInjective_of_iso
    (I.cocomplex.mapExtendIso R ComplexShape.embeddingUpNat).symm

variable [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]

/-- The required Hom comparison is constructed using the actual image complex and adjunction. -/
def imageResolutionHomAddEquiv (K : CochainComplex C ℤ) :
    (DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj
      ((I.imageComplex R).extend ComplexShape.embeddingUpNat)) ≃+
    (DerivedCategory.Q.obj ((L.mapHomologicalComplex (.up ℤ)).obj K) ⟶
      DerivedCategory.Q.obj (I.cocomplex.extend ComplexShape.embeddingUpNat)) := by
  have := adj.mapExtendedResolution_isKInjective I
  exact (Iso.homCongrAddEquiv (Iso.refl _)
    ((DerivedCategory.Q.mapIso
      (I.cocomplex.mapExtendIso R ComplexShape.embeddingUpNat)).symm)).trans
      (adj.kInjectiveHomAddEquiv K _)

end CategoryTheory.Adjunction
