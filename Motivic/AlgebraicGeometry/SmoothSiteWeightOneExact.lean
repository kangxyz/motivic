module

public import Motivic.AlgebraicGeometry.SmoothSiteBoundaryOneDivisorNorm
public import Motivic.AlgebraicGeometry.SmoothSiteReducedTorusExact
public import Motivic.AlgebraicGeometry.SmoothSiteIntegralAffineExact
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # The actual ordinary Nisnevich weight-one short exact sequence of complexes -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite
open Motivic.SmoothSiteBoundaryOneDivisor Motivic.SmoothSiteTorusDivisor
open Motivic.SmoothSiteReducedTorusExact

universe u
namespace Motivic.SmoothSiteWeightOneExact
variable (k : Type u) [Field k]

/-- The norm on each original raw singular degree. -/
abbrev rawNorm (n : ℕ) :=
  (SingularComplex.presheafMap (AlgebraicSimplex.cosimplicialSmoothSite k)
    (reducedNorm (k := k))).f n

/-- The actual degreewise divisor lands in the original raw norm kernel. -/
theorem localDivisor_norm (n : ℕ) :
    integralAffineSingularDivisor k n ≫
      whiskerLeft (SmoothSite.integralAffineInclusion k).op (rawNorm k n) = 0 := by
  apply NatTrans.ext
  funext X
  let : IsAffine X.unop.obj.left := X.unop.property.1
  let : IsIntegral X.unop.obj.left := X.unop.property.2
  exact largeAffineReducedDivisor_reducedNorm
    (X.unop.obj ⨯ AlgebraicSimplex.smoothSiteObj k n)

/-- Every genuine local degreewise divisor is injective. -/
theorem localDivisor_injective (n : ℕ)
    (X : (SmoothSite.integralAffineProperty k).FullSubcategoryᵒᵖ) :
    Function.Injective ((integralAffineSingularDivisor k n).app X) := by
  let : IsAffine X.unop.obj.left := X.unop.property.1
  let : IsIntegral X.unop.obj.left := X.unop.property.2
  exact largeAffineReducedDivisor_injective
    (X.unop.obj ⨯ AlgebraicSimplex.smoothSiteObj k n)

/-- The local degreewise image equals the kernel of the actual raw norm. -/
theorem localDivisor_exact (n : ℕ)
    (X : (SmoothSite.integralAffineProperty k).FullSubcategoryᵒᵖ)
    (z : ((rawReducedSingular k).X n).obj (op X.unop.obj))
    (hz : (rawNorm k n).app (op X.unop.obj) z = 0) :
    ∃ m, (integralAffineSingularDivisor k n).app X m = z := by
  let : IsAffine X.unop.obj.left := X.unop.property.1
  let : IsIntegral X.unop.obj.left := X.unop.property.2
  exact (reducedNorm_app_eq_zero_iff
    (X.unop.obj ⨯ AlgebraicSimplex.smoothSiteObj k n) z).mp hz

/-- Actual affine divisors identify the original raw norm kernel on the dense subsite. -/
def localKernelIso (n : ℕ) :=
  SmoothSite.integralAffineRawKernelIso k (rawNorm k n)
    (integralAffineSingularDivisor k n) (localDivisor_norm k n)
    (localDivisor_injective k n) (localDivisor_exact k n)

/-- The native sheafified kernel presentation is the already constructed original divisor. -/
theorem sheafifiedKernelDivisor (n : ℕ) :
    SmoothSite.integralAffineSheafifyMap k
      ((localKernelIso k n).hom ≫ whiskerLeft (SmoothSite.integralAffineInclusion k).op
        (kernel.ι (rawNorm k n))) = singularSheafDivisor k n := by
  exact congrArg (SmoothSite.integralAffineSheafifyMap k)
    (SmoothSite.integralAffineRawKernelIso_hom_ι k (rawNorm k n)
      (integralAffineSingularDivisor k n) (localDivisor_norm k n)
      (localDivisor_injective k n) (localDivisor_exact k n))

/-- In every degree the actual sheaf divisor is the kernel of the original reduced norm. -/
def divisorIsKernel (n : ℕ) :
    IsLimit (KernelFork.ofι ((sheafDivisorChainMap k).f n)
      (show (sheafDivisorChainMap k).f n ≫ (reducedNormSheafMap (k := k)).f n = 0 from
        congrArg (fun f => f.f n) (sheafDivisorChainMap_norm k))) := by
  exact kernel.isoKernel _ _
    (SmoothSite.integralAffineSheafifyKernelIso k (rawNorm k n) (localKernelIso k n))
    ((SmoothSite.integralAffineSheafifyKernelIso_hom_ι k (rawNorm k n)
      (localKernelIso k n)).trans (sheafifiedKernelDivisor k n))

/-- The actual reduced norm is an epimorphism of Nisnevich sheaves in every degree. -/
theorem norm_epi (n : ℕ) : Epi ((reducedNormSheafMap (k := k)).f n) := by
  apply SmoothSite.epi_sheafifyMap_of_integral_affine_surjective k (rawNorm k n)
  intro X _ _
  exact reducedNorm_app_surjective (X ⨯ AlgebraicSimplex.smoothSiteObj k n)

/-- The genuine boundary-one, reduced-torus, and unit complexes form a short complex. -/
def shortComplex := ShortComplex.mk (sheafDivisorChainMap k)
  (reducedNormSheafMap (k := k)) (sheafDivisorChainMap_norm k)

/-- The actual ordinary Nisnevich divisor sequence is short exact in all chain degrees. -/
theorem shortExact : (shortComplex k).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact {
    exact := ShortComplex.exact_of_f_is_kernel _ (divisorIsKernel k n)
    mono_f := mono_of_isLimit_fork (divisorIsKernel k n)
    epi_g := norm_epi k n }

end Motivic.SmoothSiteWeightOneExact
