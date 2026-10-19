/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.A1.LocalVanishing.Monic.NeighborhoodZero
public import Lean
/-! # Direct ordinary-cohomology and whole nonreduced divisor consumers -/
public noncomputable section
open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.PolynomialOpenQuotient
open Motivic
open _root_.AlgebraicGeometry.Scheme.SmoothSite
open _root_.CategoryTheory.Sheaf.LargeCohomology
open _root_.Motivic.SheafCohomology
open _root_.Algebra.Smooth
open _root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
universe w u
namespace MotivicTest.RelativeMonicNeighborhoodZero
variable {k R : Type u} [Field k] [CommRing R] [IsDomain R]
  [Algebra k R] [Algebra.Smooth k R]
  [HasExt.{w} (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
attribute [local instance] away_smooth
theorem original_class_whole_divisor
    (F : Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
    (n : ℕ) (f : R[X]) (hf : f.Monic)
    (e : H.{w, u + 1, u, u + 1} (nisnevichTopology (Spec (.of k))) F (n + 1)
      (lineSite (k := k) (R := R))) :
    ∃ r : R, r ≠ 0 ∧ ∃ (Y : SmoothSite (Spec (.of k)))
      (p : Y ⟶ lineSite (k := k) (R := Localization.Away r)),
      IsAffine Y.left ∧ Etale p.left ∧
      IsIso (pullback.snd p.left (inclusion (f.map (algebraMap R (Localization.Away r))))) ∧
      (presheaf.{w, u + 1, u, u + 1} (nisnevichTopology (Spec (.of k)))
        F (n + 1)).map
          (p ≫ lineMap (IsScalarTower.toAlgHom k R (Localization.Away r))).op e = 0 :=
  exists_relative_monic_neighborhood_restriction_eq_zero F n f hf e

theorem original_class_square_zero_divisor
    (F : Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
    (n : ℕ)
    (e : H.{w, u + 1, u, u + 1} (nisnevichTopology (Spec (.of k))) F (n + 1)
      (lineSite (k := k) (R := R))) :
    ∃ r : R, r ≠ 0 ∧ ∃ (Y : SmoothSite (Spec (.of k)))
      (p : Y ⟶ lineSite (k := k) (R := Localization.Away r)),
      IsAffine Y.left ∧ Etale p.left ∧
      IsIso (pullback.snd p.left
        (inclusion (((X : R[X]) ^ 2).map (algebraMap R (Localization.Away r))))) ∧
      (presheaf.{w, u + 1, u, u + 1} (nisnevichTopology (Spec (.of k)))
        F (n + 1)).map
          (p ≫ lineMap (IsScalarTower.toAlgHom k R (Localization.Away r))).op e = 0 :=
  exists_relative_monic_neighborhood_restriction_eq_zero F n (X ^ 2) (monic_X.pow 2) e

open Lean in
run_cmd do
  for name in #[``original_class_whole_divisor, ``original_class_square_zero_divisor,
      ``exists_relative_monic_neighborhood_restriction_eq_zero,
      ``exists_relative_monic_neighborhood_lift,
          ``_root_.AlgebraicGeometry.Scheme.SmoothSite.exists_affine_nisnevich_lift,
      ``Scheme.GenericSection.exists_affine_monic_neighborhood,
      ``Scheme.GenericSection.exists_monic_lift_after_localization,
      ``Scheme.Hom.exists_basicOpen_iso_over_closed_of_section] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Positive ordinary classes and full monic divisor: standard axioms only."
end MotivicTest.RelativeMonicNeighborhoodZero
