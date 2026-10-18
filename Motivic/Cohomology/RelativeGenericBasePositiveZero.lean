/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.RelativeGenericBaseH1Zero
public import Motivic.Cohomology.SheafCohomologyRelativeLineHigherVanishing

/-! # Every original positive relative affine-line class vanishes over a generic base open -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Polynomial
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.PolynomialOpenQuotient
universe w u
namespace Motivic.SheafCohomology
open RelativePolynomialOpenSpans
variable {k R : Type u} [Field k] [CommRing R] [IsDomain R]
  [Algebra k R] [Algebra.Smooth k R]
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
attribute [local instance] away_smooth

/-- Every positive original class of an HI sheaf with transfers vanishes after
actual base restrictions, retaining the entire relative affine line. -/
theorem exists_relative_generic_base_positive_zero
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant) (n : ℕ)
    (x : H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) (n + 1) (lineSite (k := k) (R := R))) :
    ∃ (r : R) (hr : r ≠ 0),
      let : IsDomain (Localization.Away r) := Localization.Away.isDomain hr
      ∃ (s : Localization.Away r) (hs : s ≠ 0),
        let : IsDomain (Localization.Away s) := Localization.Away.isDomain hs
        ∃ V : (Spec (.of (Localization.Away s))).Opens,
          IsAffineOpen V ∧ genericPoint (Spec (.of (Localization.Away s))) ∈ V ∧
          (presheaf.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
            ((SheafWithTransfers.toSheaf k).obj F) (n + 1)).map
            (SmoothSite.openInclusion (lineSite (k := k) (R := Localization.Away s))
              (boundaryBaseSourceOpen (boundaryLineProjection (Localization.Away s)) ⊤ V) ≫
                lineMap (IsScalarTower.toAlgHom k (Localization.Away r) (Localization.Away s)) ≫
                lineMap (IsScalarTower.toAlgHom k R (Localization.Away r))).op x = 0 := by
  cases n with
  | zero => exact exists_relative_generic_base_h_one_zero F hF x
  | succ n =>
    exact exists_relative_generic_base_h_add_two_zero
      ((SheafWithTransfers.toSheaf k).obj F) n x

end Motivic.SheafCohomology
