/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.DerivedCategory.ExtRightDerived
public import Motivic.Aglib.Algebra.Homology.DerivedCategory.FiniteEdge
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-! # Actual image-resolution augmentation and its derived triangle -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated HomologicalComplex
universe w v₁ v₂ u₁ u₂
namespace CategoryTheory.InjectiveResolution
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] {Y : C} (I : InjectiveResolution Y)
  (R : C ⥤ D) [R.Additive]

/-- Apply the actual functor to the actual injective resolution. -/
def imageComplex : CochainComplex D ℕ := (R.mapHomologicalComplex _).obj I.cocomplex

/-- The actual augmentation after applying the functor; no exactness is presumed. -/
def imageι : (CochainComplex.single₀ D).obj (R.obj Y) ⟶ I.imageComplex R :=
  (CochainComplex.fromSingle₀Equiv _ _).symm ⟨R.map (I.ι.f 0), by
    change R.map (I.ι.f 0) ≫ R.map (I.cocomplex.d 0 1) = 0
    rw [← R.map_comp, I.ι_f_zero_comp_complex_d, R.map_zero]⟩

@[simp]
theorem imageι_f_zero : (I.imageι R).f 0 = R.map (I.ι.f 0) :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

/-- The integer-index augmentation used for the actual derived-category cone. -/
def imageExtendedι : (CochainComplex.singleFunctor D 0).obj (R.obj Y) ⟶
    (I.imageComplex R).extend ComplexShape.embeddingUpNat :=
  (extendSingleIso ComplexShape.embeddingUpNat (R.obj Y) 0 0 rfl).inv ≫
    extendMap (I.imageι R) ComplexShape.embeddingUpNat

variable [HasInjectiveResolutions C]

/-- The homology of the actual image complex is the actual right-derived functor. -/
def imageExtendedHomologyIso (n : ℕ) :
    ((I.imageComplex R).extend ComplexShape.embeddingUpNat).homology (n : ℤ) ≅
      (R.rightDerived n).obj Y :=
  (I.imageComplex R).extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl ≪≫
    (I.isoRightDerivedObj R n).symm

variable [HasDerivedCategory.{w} D]

/-- The distinguished triangle is constructed from the actual augmentation, not input. -/
def imageTriangle : CategoryTheory.Pretriangulated.Triangle (DerivedCategory D) :=
  DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle (I.imageExtendedι R))

omit [HasInjectiveResolutions C] in
theorem imageTriangle_distinguished :
    I.imageTriangle R ∈ distTriang (DerivedCategory D) :=
  DerivedCategory.mappingCone_triangle_distinguished _

end CategoryTheory.InjectiveResolution
