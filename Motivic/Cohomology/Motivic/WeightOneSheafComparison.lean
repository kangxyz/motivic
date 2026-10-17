/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.OrdinaryShiftComparison
public import Motivic.AlgebraicGeometry.SmoothSiteWeightOneQuasiIso
public import Motivic.AlgebraicGeometry.SmoothSiteUnitSheafification
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-! # The weight-one comparison for the original ordinary motivic sheaf complex -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic

variable (k : Type u) [Field k]

/-- The actual ordinary reduced-torus singular sheaf complex maps to genuine
units concentrated in chain degree zero. -/
def weightOneSheafChainComparison :
    SingularComplex.sheafObj (SmoothSite.nisnevichTopology (Spec (.of k)))
      (AlgebraicSimplex.cosimplicialSmoothSite k)
      ((PresheafWithTransfers.toPresheaf k).obj (PresheafWithTransfers.reducedTorus k 1)) ⟶
        (ChainComplex.single₀ _).obj (SmoothSite.largeUnitsSheaf (Spec (.of k))) :=
  SmoothSiteTorusDivisor.reducedNormSheafMap ≫
    (SmoothSite.unitSheafifiedSingularIso k).hom ≫
      (SmoothSite.unitSingularSheafHomotopyEquiv k).hom

instance weightOneSheafChainComparison_quasiIso :
    QuasiIso (weightOneSheafChainComparison k) := by
  unfold weightOneSheafChainComparison
  infer_instance

/-- The canonical weight-one map starts at the original motivic sheaf complex
and ends at the genuine global-unit sheaf in mathlib's signed shift `[-1]`. -/
def weightOneSheafComparison :
    motivicSheafComplex k 1 ⟶
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        (SmoothSite.largeUnitsSheaf (Spec (.of k))))⟦(-1 : ℤ)⟧ :=
  (motivicSheafComplexOrdinaryShiftIso k 1).hom ≫
    (shiftFunctor _ (-1 : ℤ)).map
      (HomologicalComplex.extendMap (weightOneSheafChainComparison k)
        (ComplexShape.embeddingUpIntLE 0) ≫
      (HomologicalComplex.extendSingleIso (ComplexShape.embeddingUpIntLE 0)
        (SmoothSite.largeUnitsSheaf (Spec (.of k))) 0 0 (by simp)).hom)

/-- The full original ordinary Nisnevich comparison is a quasi-isomorphism. -/
instance weightOneSheafComparison_quasiIso : QuasiIso (weightOneSheafComparison k) := by
  unfold weightOneSheafComparison
  infer_instance

end Motivic
