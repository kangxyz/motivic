/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Sheaves.IntegralAffineSheafification
public import Motivic.Aglib.CategoryTheory.SheafifyAdditive
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Exactness of actual sheafifications from integral affine kernel presentations -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite

universe u
namespace AlgebraicGeometry.Scheme.SmoothSite
variable (k : Type u) [Field k]

/-- Pointwise injectivity and exactness give the actual kernel on the dense subsite. -/
def integralAffineKernelLimit
    {A B C : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (g : B ⟶ C)
    (α : (integralAffineInclusion k).op ⋙ A ⟶ (integralAffineInclusion k).op ⋙ B)
    (hz : α ≫ whiskerLeft (integralAffineInclusion k).op g = 0)
    (hi : ∀ X, Function.Injective (α.app X))
    (he : ∀ X (z : B.obj ((integralAffineInclusion k).op.obj X)),
      g.app _ z = 0 → ∃ m, α.app X m = z) :
    IsLimit (KernelFork.ofι α hz) := by
  apply evaluationJointlyReflectsLimits
  intro X
  refine (KernelFork.isLimitMapConeEquiv _ _).symm ?_
  let S : ShortComplex AddCommGrpCat.{u + 1} :=
    ShortComplex.mk (α.app X) (g.app _) (congrArg (fun η => η.app X) hz)
  have hm : Mono S.f := (AddCommGrpCat.mono_iff_injective _).mpr (hi X)
  have hS : S.Exact := (S.ab_exact_iff).mpr (he X)
  exact hS.fIsKernel

/-- The local kernel presentation agrees with restriction of the original raw kernel. -/
def integralAffineRawKernelIso
    {A B C : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (g : B ⟶ C)
    (α : (integralAffineInclusion k).op ⋙ A ⟶ (integralAffineInclusion k).op ⋙ B)
    (hz : α ≫ whiskerLeft (integralAffineInclusion k).op g = 0)
    (hi : ∀ X, Function.Injective (α.app X))
    (he : ∀ X (z : B.obj ((integralAffineInclusion k).op.obj X)),
      g.app _ z = 0 → ∃ m, α.app X m = z) :
    (integralAffineInclusion k).op ⋙ A ≅ (integralAffineInclusion k).op ⋙ kernel g :=
  (integralAffineKernelLimit k g α hz hi he).conePointUniqueUpToIso
    (KernelFork.mapIsLimit _ (kernelIsKernel g)
      ((whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj (integralAffineInclusion k).op))

/-- The raw kernel isomorphism retains its original inclusion. -/
theorem integralAffineRawKernelIso_hom_ι
    {A B C : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (g : B ⟶ C)
    (α : (integralAffineInclusion k).op ⋙ A ⟶ (integralAffineInclusion k).op ⋙ B)
    (hz : α ≫ whiskerLeft (integralAffineInclusion k).op g = 0)
    (hi : ∀ X, Function.Injective (α.app X))
    (he : ∀ X (z : B.obj ((integralAffineInclusion k).op.obj X)),
      g.app _ z = 0 → ∃ m, α.app X m = z) :
    (integralAffineRawKernelIso k g α hz hi he).hom ≫
      whiskerLeft (integralAffineInclusion k).op (kernel.ι g) = α :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

/-- A genuine local presentation of the raw kernel presents the sheafified kernel. -/
def integralAffineSheafifyKernelIso
    {A B C : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (g : B ⟶ C)
    (e : (integralAffineInclusion k).op ⋙ A ≅
      (integralAffineInclusion k).op ⋙ kernel g) :
    (presheafToSheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).obj A ≅
      kernel ((presheafToSheaf (nisnevichTopology (Spec (.of k)))
        AddCommGrpCat.{u + 1}).map g) :=
  integralAffineSheafifyIso k e ≪≫ PreservesKernel.iso
    (presheafToSheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}) g

/-- The kernel comparison retains exactly the original local divisor map. -/
theorem integralAffineSheafifyKernelIso_hom_ι
    {A B C : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (g : B ⟶ C)
    (e : (integralAffineInclusion k).op ⋙ A ≅
      (integralAffineInclusion k).op ⋙ kernel g) :
    (integralAffineSheafifyKernelIso k g e).hom ≫
      kernel.ι ((presheafToSheaf (nisnevichTopology (Spec (.of k)))
        AddCommGrpCat.{u + 1}).map g) =
      integralAffineSheafifyMap k
        (e.hom ≫ whiskerLeft (integralAffineInclusion k).op (kernel.ι g)) := by
  dsimp only [integralAffineSheafifyKernelIso, Iso.trans_hom, integralAffineSheafifyIso]
  rw [Category.assoc, PreservesKernel.iso_hom, kernelComparison_comp_ι,
    integralAffineSheafifyMap_comp, integralAffineSheafifyMap_whisker]

/-- The genuine sheafified local divisor is the kernel of the sheafified raw norm. -/
def integralAffineSheafifyMapIsKernel
    {A B C : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (g : B ⟶ C)
    (e : (integralAffineInclusion k).op ⋙ A ≅
      (integralAffineInclusion k).op ⋙ kernel g) :
    IsLimit (KernelFork.ofι (f := (presheafToSheaf
      (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).map g)
      (integralAffineSheafifyMap k
        (e.hom ≫ whiskerLeft (integralAffineInclusion k).op (kernel.ι g))) (by
      rw [← integralAffineSheafifyKernelIso_hom_ι, Category.assoc, kernel.condition,
        comp_zero])) :=
  kernel.isoKernel _ _ (integralAffineSheafifyKernelIso k g e)
    (integralAffineSheafifyKernelIso_hom_ι k g e)

end AlgebraicGeometry.Scheme.SmoothSite
