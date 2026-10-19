/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.Sheaf.LaurentGenericZero
public import Lean
/-! # Original positive ordinary cohomology, with precisely the current-degree HI premise -/
public noncomputable section
open _root_.AlgebraicGeometry.Scheme.SmoothSite (nisnevichTopology)
open CategoryTheory AlgebraicGeometry Polynomial Motivic
open _root_.Algebra.Smooth
open _root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
open _root_.CategoryTheory.Sheaf.LargeCohomology
open _root_.Motivic.SheafCohomology
universe w u
namespace MotivicTest.SheafCohomologyLaurentGenericZero
open _root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
attribute [local instance] away_smooth

/-- Neither field-value sheafification nor strict invariance is an input. -/
theorem actual_ordinary_class_dies (k R : Type u) [Field k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.Smooth k R]
    [HasExt.{w} (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
    (F : SheafWithTransfers.{u + 1} k) (n : ℕ)
    (hP : (withTransfers k F (n + 1)).IsA1Invariant)
    (e : H.{w, u + 1, u, u + 1} (nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) (n + 1) (openSite (k := k) (X : R[X]))) :
    ∃ r : R, r ≠ 0 ∧
      (presheaf (nisnevichTopology (Spec (.of k)))
        ((SheafWithTransfers.toSheaf k).obj F) (n + 1)).map
          (puncturedBaseMap (IsScalarTower.toAlgHom k R (Localization.Away r))).op e = 0 :=
  exists_laurent_base_shrink_succ_eq_zero k R F n hP e

open Lean in
run_cmd do
  for name in #[``actual_ordinary_class_dies, ``exists_laurent_base_shrink_succ_eq_zero,
      ``exists_base_shrink_of_neighborhood_zero] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original ordinary cohomology after actual base shrinking: standard foundations only."

end MotivicTest.SheafCohomologyLaurentGenericZero
