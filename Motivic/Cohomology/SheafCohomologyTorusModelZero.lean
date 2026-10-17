/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.SheafCohomologyLaurentGenericZero
public import Motivic.AlgebraicGeometry.Correspondences.RelativeLaurentProductMap
public import Motivic.AlgebraicGeometry.PresheavesWithTransfers.GraphSquareZero
/-! # Eventual zero of the original torus-sections presheaf on actual affine models -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Polynomial Opposite
universe w u
namespace Motivic.SheafCohomology
open RelativePolynomialOpenSpans PresheafWithTransfers
variable (k R : Type u) [Field k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.Smooth k R]
    [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
attribute [local instance] away_smooth

/-- The unchanged torus-sections presheaf, with its actual coefficient localization graph. -/
theorem exists_torus_model_base_shrink_succ_eq_zero
    (F : SheafWithTransfers.{u + 1} k) (n : ℕ)
    (hP : (withTransfers k F (n + 1)).IsA1Invariant)
    (s : sections (torusSections (withTransfers k F (n + 1)))
      (Cor.mk (sourceSite (k := k) (A := R)))) :
    ∃ r : R, r ≠ 0 ∧
      (torusSections (withTransfers k F (n + 1))).transfer ((Cor.graphFunctor k).map
        (AffineTorusPolynomialPresentation.affineMorphism
          (IsScalarTower.toAlgHom k R (Localization.Away r)))) s = 0 := by
  let P := withTransfers k F (n + 1)
  let e := P.transfer ((Cor.graphFunctor k).map (puncturedProductIso (k := k) (R := R)).hom) s
  obtain ⟨r, hr, he⟩ := exists_laurent_base_shrink_succ_eq_zero k R F n hP e
  let φ := IsScalarTower.toAlgHom k R (Localization.Away r)
  have he' : P.transfer ((Cor.graphFunctor k).map (puncturedBaseMap φ)) e = 0 :=
    (withTransfers_graph k F (n + 1) (puncturedBaseMap φ) e).trans he
  refine ⟨r, hr, ?_⟩
  change (torusSections P).transfer ((Cor.graphFunctor k).map
    (AffineTorusPolynomialPresentation.affineMorphism φ)) s = 0
  rw [torusSections_graph]
  exact transfer_zero_of_iso_square P (puncturedProductIso (k := k) (R := R))
    (puncturedProductIso (k := k) (R := Localization.Away r)) (puncturedBaseMap φ)
    _ (puncturedProductIso_naturality φ) s he'

end Motivic.SheafCohomology
