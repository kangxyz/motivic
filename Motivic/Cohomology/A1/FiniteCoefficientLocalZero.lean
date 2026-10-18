/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.FiniteIntegralAffineLocalZero
public import Motivic.Cohomology.A1.CoefficientLocalZero

/-! # Actual finite-field coefficient local-zero input and dense restriction

The arbitrary-coefficient-universe geometric producer supplies the existing
upper coefficient contract at universe `u + 1`. For a Nisnevich sheaf with
transfers, the existing separatedness argument then gives zero detection and
monicity of the literal dense-open restriction. No presentation family or
boundary epimorphism is assumed or asserted.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Motivic

universe u

namespace Motivic.PresheafWithTransfers

/-- Actual finite-field geometry supplies the original integral-affine coefficient input. -/
theorem integralAffineLocalZero_of_finite (k : Type u) [Field k] [Finite k] :
    IntegralAffineLocalZero k := by
  intro X A _ _ _ a _ P hP v hv x
  exact exists_finite_zero_neighborhood_of_integral_affine a P hP v hv x

end Motivic.PresheafWithTransfers

namespace Motivic.SheafWithTransfers

/-- A section of an original HI Nisnevich sheaf over a finite field is detected
by its actual dense-open restriction. Separatedness is used only at this stage. -/
theorem section_eq_zero_of_dense_open_of_finite
    {k : Type u} [Field k] [Finite k] {X A : SmoothSite (Spec (.of k))}
    (a : A ⟶ X) [IsOpenImmersion a.left] (ha : DenseRange a.left)
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant)
    (s : F.obj.sections (Cor.mk X))
    (hs : F.obj.transfer ((Cor.graphFunctor k).map a) s = 0) : s = 0 :=
  section_eq_zero_of_dense_open_of_integralAffineLocalZero
    (PresheafWithTransfers.integralAffineLocalZero_of_finite k) a ha F hF s hs

end Motivic.SheafWithTransfers

namespace Motivic.FiniteEtaleSite

/-- The literal small-site restriction of an original HI Nisnevich sheaf to a
dense open is monic over a finite field, with no supplied local-zero family. -/
theorem restrictionToDirectImage_mono_of_dense_of_finite
    {k : Type u} [Field k] [Finite k]
    {U Y : SmoothSite (Spec (.of k))} (j : U ⟶ Y) [IsOpenImmersion j.left]
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant)
    (hj : DenseRange j.left) :
    Mono (restrictionToDirectImage ((SheafWithTransfers.toSheaf k).obj F) j) :=
  restrictionToDirectImage_mono_of_dense_of_integralAffineLocalZero
    (PresheafWithTransfers.integralAffineLocalZero_of_finite k) j F hF hj

end Motivic.FiniteEtaleSite
