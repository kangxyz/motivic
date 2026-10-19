/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.FlatBaseChangeLocalization

/-! Consumers for flat base change and literal module localization of actual Tor. -/

@[expose] public section

open CategoryTheory

universe u

namespace Motivic.MotivicTest.TorComparisonFlatBaseChange

/-- The comparison applies to arbitrary modules and every degree. -/
noncomputable def arbitraryModules {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Flat) (M N : ModuleCat.{u} R) (n : ℕ) :
    (ModuleCat.extendScalars f).obj (((Tor (ModuleCat R) n).obj M).obj N) ≅
      ((Tor (ModuleCat S) n).obj ((ModuleCat.extendScalars f).obj M)).obj
        ((ModuleCat.extendScalars f).obj N) :=
  _root_.ModuleCat.TorComparison.flatBaseChangeTorIso f hf M N n

/-- Support quotients require no flatness or regularity assumptions. -/
noncomputable def arbitrarySupportIdeals {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Flat) (I J : Ideal R) (n : ℕ) :
    (ModuleCat.extendScalars f).obj
        (((Tor (ModuleCat R) n).obj (ModuleCat.of R (R ⧸ I))).obj
          (ModuleCat.of R (R ⧸ J))) ≅
      ((Tor (ModuleCat S) n).obj
        ((ModuleCat.extendScalars f).obj (ModuleCat.of R (R ⧸ I)))).obj
        ((ModuleCat.extendScalars f).obj (ModuleCat.of R (R ⧸ J))) :=
  _root_.ModuleCat.TorComparison.flatBaseChangeTorIso f hf _ _ n

/-- Every term of the constructed scalar-extended resolution is projective. -/
theorem extendedResolutionProjective {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Flat) (N : ModuleCat.{u} R) (n : ℕ) :
    Projective ((_root_.ModuleCat.TorComparison.flatExtendProjectiveResolution f hf
      (projectiveResolution N)).complex.X n) := inferInstance

/-- The augmentation of that actual resolution is genuinely a quasi-isomorphism. -/
theorem extendedResolutionQuasiIso {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Flat) (N : ModuleCat.{u} R) :
    QuasiIso (_root_.ModuleCat.TorComparison.flatExtendProjectiveResolution f hf
      (projectiveResolution N)).π := inferInstance

/-- Localizing actual support quotients gives Tor of literal localized modules. -/
noncomputable def localizedSupportIdeals {R : Type u} [CommRing R]
    (p : Submonoid R) (I J : Ideal R) (n : ℕ) :
    ModuleCat.of (Localization p) (LocalizedModule p
        (((Tor (ModuleCat R) n).obj (ModuleCat.of R (R ⧸ I))).obj
          (ModuleCat.of R (R ⧸ J)))) ≅
      ((Tor (ModuleCat (Localization p)) n).obj
        (ModuleCat.of (Localization p) (LocalizedModule p (R ⧸ I)))).obj
        (ModuleCat.of (Localization p) (LocalizedModule p (R ⧸ J))) :=
  _root_.ModuleCat.TorComparison.localizedTorIso p _ _ n

/-- Actual prime-local scalar structures are present in both Tor arguments. -/
noncomputable def primeLocalizedModules {R : Type u} [CommRing R]
    (P : Ideal R) [P.IsPrime] (M N : ModuleCat.{u} R) (n : ℕ) :
    ModuleCat.of (Localization.AtPrime P)
        (LocalizedModule P.primeCompl (((Tor (ModuleCat R) n).obj M).obj N)) ≅
      ((Tor (ModuleCat (Localization.AtPrime P)) n).obj
        (ModuleCat.of (Localization.AtPrime P) (LocalizedModule P.primeCompl M))).obj
        (ModuleCat.of (Localization.AtPrime P) (LocalizedModule P.primeCompl N)) :=
  _root_.ModuleCat.TorComparison.primeLocalizedTorIso P M N n

/-- The degree-zero endpoint is included, with no positivity restriction. -/
noncomputable def degreeZero {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Flat) (M N : ModuleCat.{u} R) :
    (ModuleCat.extendScalars f).obj (((Tor (ModuleCat R) 0).obj M).obj N) ≅
      ((Tor (ModuleCat S) 0).obj ((ModuleCat.extendScalars f).obj M)).obj
        ((ModuleCat.extendScalars f).obj N) :=
  _root_.ModuleCat.TorComparison.flatBaseChangeTorIso f hf M N 0

end Motivic.MotivicTest.TorComparisonFlatBaseChange
