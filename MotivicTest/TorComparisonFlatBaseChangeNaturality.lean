/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.TorComparison.FlatBaseChangeNaturality
public import Motivic.Algebra.Homology.TorComparison.FlatBaseChangeLocalization

/-!
# Consumers for canonical Tor base-change naturality

The principal-localization squares use arbitrary actual module morphisms in both
Tor arguments. Resolution independence is tested against the already existing
canonical comparison. These are module-naturality gates, not scalar-map
composition or nonvanishing claims.
-/

@[expose] public section

open CategoryTheory

universe u

namespace Motivic.MotivicTest.TorComparisonFlatBaseChangeNaturality

variable {R : Type u} [CommRing R]

/-- Principal localization uses the actual canonical ring map and its proved flatness. -/
theorem principalCoefficientSquare (r : R) {M M' : ModuleCat.{u} R} (u : M ⟶ M')
    (N : ModuleCat.{u} R) (n : ℕ) :
    (ModuleCat.extendScalars (algebraMap R (Localization.Away r))).map
        (((Tor (ModuleCat R) n).map u).app N) ≫
        (TorComparison.flatBaseChangeTorIso (algebraMap R (Localization.Away r))
          (RingHom.flat_algebraMap_iff.mpr
            (IsLocalization.flat (Localization.Away r) (Submonoid.powers r))) M' N n).hom =
      (TorComparison.flatBaseChangeTorIso (algebraMap R (Localization.Away r))
        (RingHom.flat_algebraMap_iff.mpr
          (IsLocalization.flat (Localization.Away r) (Submonoid.powers r))) M N n).hom ≫
        ((Tor (ModuleCat (Localization.Away r)) n).map
          ((ModuleCat.extendScalars (algebraMap R (Localization.Away r))).map u)).app
            ((ModuleCat.extendScalars (algebraMap R (Localization.Away r))).obj N) :=
  TorComparison.flatBaseChangeTorIso_hom_naturality_left _ _ u N n

/-- The resolved module may vary by any morphism, without a flatness hypothesis on it. -/
theorem principalResolvedSquare (r : R) (M : ModuleCat.{u} R)
    {N N' : ModuleCat.{u} R} (v : N ⟶ N') (n : ℕ) :
    (ModuleCat.extendScalars (algebraMap R (Localization.Away r))).map
        (((Tor (ModuleCat R) n).obj M).map v) ≫
        (TorComparison.flatBaseChangeTorIso (algebraMap R (Localization.Away r))
          (RingHom.flat_algebraMap_iff.mpr
            (IsLocalization.flat (Localization.Away r) (Submonoid.powers r))) M N' n).hom =
      (TorComparison.flatBaseChangeTorIso (algebraMap R (Localization.Away r))
        (RingHom.flat_algebraMap_iff.mpr
          (IsLocalization.flat (Localization.Away r) (Submonoid.powers r))) M N n).hom ≫
        ((Tor (ModuleCat (Localization.Away r)) n).obj
          ((ModuleCat.extendScalars (algebraMap R (Localization.Away r))).obj M)).map
            ((ModuleCat.extendScalars (algebraMap R (Localization.Away r))).map v) :=
  TorComparison.flatBaseChangeTorIso_hom_naturality_right _ _ M v n

/-- Arbitrary support ideals, including nonradical ideals, retain resolution independence. -/
theorem supportQuotientResolutionIndependent (r : R) (I J : Ideal R)
    (P : ProjectiveResolution (ModuleCat.of R (R ⧸ J))) (n : ℕ) :
    TorComparison.flatBaseChangeTorIsoOfResolution (algebraMap R (Localization.Away r))
        (RingHom.flat_algebraMap_iff.mpr
          (IsLocalization.flat (Localization.Away r) (Submonoid.powers r)))
        (ModuleCat.of R (R ⧸ I)) P n =
      TorComparison.flatBaseChangeTorIso (algebraMap R (Localization.Away r))
        (RingHom.flat_algebraMap_iff.mpr
          (IsLocalization.flat (Localization.Away r) (Submonoid.powers r)))
        (ModuleCat.of R (R ⧸ I)) (ModuleCat.of R (R ⧸ J)) n :=
  TorComparison.flatBaseChangeTorIsoOfResolution_eq_flatBaseChangeTorIso _ _ _ P n

end Motivic.MotivicTest.TorComparisonFlatBaseChangeNaturality
