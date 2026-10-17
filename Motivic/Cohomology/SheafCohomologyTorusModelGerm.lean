/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.SheafCohomologyTorusModelZero
public import Motivic.Cohomology.A1.PresheafModelGenericZero
/-! # Actual generic smooth-model colimits of torus and contraction sections vanish -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
universe w u
namespace Motivic.SheafCohomology
open PresheafWithTransfers
attribute [local instance] RelativePolynomialOpenSpans.away_smooth
variable (k : Type u) [Field k]
    [HasExt.{max w (u + 1)}
      (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The affine-localization premise is proved, not supplied by the caller. -/
theorem torus_affineLocalizationZero (F : SheafWithTransfers.{u + 1} k) (n : ℕ)
    (hP : (withTransfers k F (n + 1)).IsA1Invariant) :
    AffineLocalizationZero (torusSections (withTransfers k F (n + 1))) := by
  intro R _ _ _ _ s
  exact exists_torus_model_base_shrink_succ_eq_zero k R F n hP s

/-- The unchanged filtered colimit over all generic-point neighborhoods of the actual model.
No function-field spectrum is inserted into Sm/k and no sheafification exchange is used. -/
theorem torus_genericModelGerm_succ_eq_zero (F : SheafWithTransfers.{u + 1} k) (n : ℕ)
    (hP : (withTransfers k F (n + 1)).IsA1Invariant)
    (X : SmoothSite (Spec (.of k))) [IsIntegral X.left]
    (s : genericModelGerm (torusSections (withTransfers k F (n + 1))) X) : s = 0 :=
  genericModelGerm_eq_zero _ (torus_affineLocalizationZero k F n hP) X s

/-- The original quotient's representatives inherit the proved base-localization zero. -/
theorem contraction_affineLocalizationZero (F : SheafWithTransfers.{u + 1} k) (n : ℕ)
    (hP : (withTransfers k F (n + 1)).IsA1Invariant) :
    AffineLocalizationZero (contraction (withTransfers k F (n + 1))) := by
  let P := withTransfers k F (n + 1)
  intro R _ _ _ _ s
  obtain ⟨t, rfl⟩ := toContraction_surjective P (Cor.mk
    (AffineTorusPolynomialPresentation.affineSite k R)) s
  obtain ⟨r, hr, hz⟩ := torus_affineLocalizationZero k F n hP R t
  refine ⟨r, hr, ?_⟩
  have h := ConcreteCategory.congr_hom (toContraction_naturality P
    ((Cor.graphFunctor k).map (AffineTorusPolynomialPresentation.affineMorphism
      (IsScalarTower.toAlgHom k R (Localization.Away r))))) t
  rw [ConcreteCategory.comp_apply, hz] at h
  exact h.symm.trans (map_zero ((toContraction P).hom.app _).hom)

/-- This proves generic-model contraction germs vanish, not that the contraction sheaf is zero. -/
theorem contraction_genericModelGerm_succ_eq_zero (F : SheafWithTransfers.{u + 1} k) (n : ℕ)
    (hP : (withTransfers k F (n + 1)).IsA1Invariant)
    (X : SmoothSite (Spec (.of k))) [IsIntegral X.left]
    (s : genericModelGerm (contraction (withTransfers k F (n + 1))) X) : s = 0 :=
  genericModelGerm_eq_zero _ (contraction_affineLocalizationZero k F n hP) X s

end Motivic.SheafCohomology
