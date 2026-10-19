module
public import Motivic.Cohomology.RelativeGenericBaseH1Zero
public import Lean
/-! # Every original relative affine-line H¹ class vanishes over a generic base open -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Polynomial
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.PolynomialOpenQuotient
universe w u
namespace MotivicTests.RelativeGenericBaseH1Zero
open Motivic Motivic.SheafCohomology
open Motivic.RelativePolynomialOpenSpans
variable {k R : Type u} [Field k] [CommRing R] [IsDomain R]
  [Algebra k R] [Algebra.Smooth k R]
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
attribute [local instance] away_smooth

theorem original_model_class_zero
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant)
    (x : H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) 1 (lineSite (k := k) (R := R))) :
    ∃ (r : R) (hr : r ≠ 0),
      let : IsDomain (Localization.Away r) := Localization.Away.isDomain hr
      ∃ (s : Localization.Away r) (hs : s ≠ 0),
        let : IsDomain (Localization.Away s) := Localization.Away.isDomain hs
        ∃ V : (Spec (.of (Localization.Away s))).Opens,
          IsAffineOpen V ∧ genericPoint (Spec (.of (Localization.Away s))) ∈ V ∧
          (presheaf.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
            ((SheafWithTransfers.toSheaf k).obj F) 1).map
            (SmoothSite.openInclusion (lineSite (k := k) (R := Localization.Away s))
              (boundaryBaseSourceOpen (boundaryLineProjection (Localization.Away s)) ⊤ V) ≫
                lineMap (IsScalarTower.toAlgHom k (Localization.Away r) (Localization.Away s)) ≫
                lineMap (IsScalarTower.toAlgHom k R (Localization.Away r))).op x = 0 :=
  exists_relative_generic_base_h_one_zero F hF x

open Lean in
run_cmd do
  for name in #[``original_model_class_zero, ``exists_relative_generic_base_h_one_zero,
      ``exists_monic_h_one_base_open_zero,
      ``Scheme.RelativeAffineLineEtaleCompactification.exists_original_h_one_base_restriction_eq_zero]
      do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original relative model H1 generic-base zero: standard axioms only."
end MotivicTests.RelativeGenericBaseH1Zero
