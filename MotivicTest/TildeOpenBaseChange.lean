/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Modules.TildeOpenBaseChange
public import MotivicTest.TorQuotientFiniteness

/-! # Actual principal-open restriction of tilde, including supported nonzero higher Tor -/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct ChangeOfRings

universe u

namespace Motivic.MotivicTest.TildeOpenBaseChange

open Motivic.TildeOpenBaseChange Motivic.TorComparison TorQuotientFiniteness

/-- Every principal localization gives the actual natural tilde/open comparison. -/
def principalIso (A : CommRingCat.{u}) (r : A) :
    tilde.functor A ⋙ Scheme.Modules.restrictFunctor
        (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away r)))) ≅
      ModuleCat.extendScalars (algebraMap A (Localization.Away r)) ⋙
        tilde.functor (CommRingCat.of (Localization.Away r)) :=
  restrictionIso (CommRingCat.ofHom (algebraMap A (Localization.Away r)))

/-- Principal-open restriction is natural for every actual ambient module morphism. -/
theorem principal_naturality (A : CommRingCat.{u}) (r : A)
    {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    (Scheme.Modules.restrictFunctor
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away r))))).map (tilde.map f) ≫
        (principalIso A r).hom.app N =
      (principalIso A r).hom.app M ≫
        tilde.map ((ModuleCat.extendScalars (algebraMap A (Localization.Away r))).map f) :=
  restrictionIso_naturality _ f

/-- The coordinate of the actual principal-open adjoint comparison is the pure tensor `1 ⊗ m`. -/
theorem principal_unit_coordinate (A : CommRingCat.{u}) (r : A)
    (M : ModuleCat.{u} A) (m : M) :
    (((tilde.adjunction (R := A)).comp
      (Scheme.Modules.restrictAdjunction
        (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away r)))))).homEquiv M _
        ((principalIso A r).hom.app M) ≫
      (Motivic.AffinePushforward.globalSectionsIso
        (CommRingCat.ofHom (algebraMap A (Localization.Away r)))).hom.app
        (tilde ((ModuleCat.extendScalars (algebraMap A (Localization.Away r))).obj M))) m =
      (tilde.isoTop (R := CommRingCat.of (Localization.Away r))
        ((ModuleCat.extendScalars (algebraMap A (Localization.Away r))).obj M)).hom
        ((1 : Localization.Away r) ⊗ₜ[A,algebraMap A (Localization.Away r)] m) :=
  restrictionIso_globalSections_apply _ M m

/-- The actual supported degree-one Tor is sheafified on its genuine quotient support ring. -/
def higherTorPrincipalIso :=
  (principalIso (CommRingCat.of (ℤ ⧸ (fourIdeal ⊔ fourIdeal))) 3).app
    (torSupportModule fourIdeal fourIdeal 1)

/-- The actual supported module in the tilde/open comparison is not zero. -/
theorem higherTorSupport_nonzero : ¬ Limits.IsZero (torSupportModule fourIdeal fourIdeal 1) := by
  intro h
  apply higherTor_nonzero
  apply ModuleCat.isZero_iff_subsingleton.mpr
  have hs := ModuleCat.subsingleton_of_isZero h
  exact hs

/-- The original ideal underlying that support is nonradical. -/
theorem higherTorIdeal_not_radical : ¬ fourIdeal.IsRadical := fourIdeal_not_radical

end Motivic.MotivicTest.TildeOpenBaseChange
