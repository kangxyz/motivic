/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.AffineLine.GenericBase
import Lean

namespace MotivicTest.SheafCohomologyRelativeLineHigherVanishing

/-! # Direct original relative-line endpoint and full transitive trust audit -/

public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Hom
open Motivic Motivic.SheafCohomology Motivic.RelativePolynomialOpenSpans
universe w u
variable {k R : Type u} [Field k] [CommRing R] [IsDomain R]
  [Algebra k R] [Algebra.Smooth k R]
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
attribute [local instance] away_smooth

/-- An arbitrary ordinary sheaf, arbitrary smooth integral affine base, and the
literal original Ext restriction. No transfers or homotopy invariance premise. -/
theorem original_relative_line_higher_class_eventually_zero
    (F : Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
    (n : ℕ)
    (x : H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      F (n + 2) (lineSite (k := k) (R := R))) :
    ∃ (r : R) (hr : r ≠ 0),
      let : IsDomain (Localization.Away r) := Localization.Away.isDomain hr
      ∃ (s : Localization.Away r) (hs : s ≠ 0),
        let : IsDomain (Localization.Away s) := Localization.Away.isDomain hs
        ∃ V : (Spec (.of (Localization.Away s))).Opens,
          IsAffineOpen V ∧ genericPoint (Spec (.of (Localization.Away s))) ∈ V ∧
          (presheaf.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
            F (n + 2)).map
            (SmoothSite.openInclusion (lineSite (k := k) (R := Localization.Away s))
              (boundaryBaseSourceOpen (boundaryLineProjection (Localization.Away s)) ⊤ V) ≫
                lineMap (IsScalarTower.toAlgHom k (Localization.Away r) (Localization.Away s)) ≫
                lineMap (IsScalarTower.toAlgHom k R (Localization.Away r))).op x = 0 :=
  exists_relative_generic_base_h_add_two_zero F n x

open Lean in
run_cmd do
  for name in #[``original_relative_line_higher_class_eventually_zero,
      ``exists_relative_generic_base_h_add_two_zero,
      ``exists_relativeLine_base_open_restriction_eq_zero_of_zero_square,
      ``exists_relative_monic_open_restriction_eq_zero,
      ``exists_relative_monic_positive_zero_square,
      ``ordinary_restriction_eq_zero_of_square_refinement,
      ``ordinaryOpenBaseSquare_iso_complement,
      ``Scheme.exists_base_principal_openImmersion_overlap_shrinking,
      ``Scheme.Hom.isIso_pullback_snd_of_open_source_of_mono_base,
      ``AlgebraicGeometry.PolynomialOpenQuotient.range_inclusion_complement] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original relative-line H^(n+2), base shrinking only: standard foundations only."

end MotivicTest.SheafCohomologyRelativeLineHigherVanishing
