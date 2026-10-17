/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Intersection.SpecTor
public import Motivic.Algebra.Homology.TorComparison.FlatBaseChangeLocalization
public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization

/-!
# Closed affine coordinate localization and actual stalk Tor

A surjective coordinate map identifies localization of the coordinate module
at the ambient prime with the actual local ring of the source. The map on
localized scalars is the literal `Localization.localRingHom`. This bridge
is specific to surjective maps and makes no assertion for general finite maps.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic.Intersection

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]

/-- The affine coordinate ring with the action of its specified coordinate map. -/
def specCoordinateModule (f : R →+* A) : ModuleCat R :=
  (ModuleCat.restrictScalars f).obj (ModuleCat.of A A)

set_option backward.isDefEq.respectTransparency false in
/-- A surjective coordinate map makes ambient-prime module localization the
actual source local ring, with the literal common-prime localized scalar map. -/
def closedPrimeLocalizedModuleIso (f : R →+* A) (hf : Function.Surjective f)
    (P : Ideal R) [P.IsPrime] (Q : Ideal A) [Q.IsPrime] (hPQ : P = Q.comap f) :
    ModuleCat.of (Localization.AtPrime P)
      (LocalizedModule P.primeCompl (specCoordinateModule f)) ≅
      (ModuleCat.restrictScalars (Localization.localRingHom P Q f hPQ)).obj
        (ModuleCat.of (Localization.AtPrime Q) (Localization.AtPrime Q)) := by
  letI : Algebra R A := f.toAlgebra
  letI : Algebra (Localization.AtPrime P) (Localization.AtPrime Q) :=
    (Localization.localRingHom P Q f hPQ).toAlgebra
  letI : IsScalarTower R (Localization.AtPrime P) (Localization.AtPrime Q) :=
    .of_algebraMap_eq fun x ↦ by
      rw [IsScalarTower.algebraMap_apply R A (Localization.AtPrime Q)]
      change algebraMap A (Localization.AtPrime Q) (f x) =
        Localization.localRingHom P Q f hPQ (algebraMap R (Localization.AtPrime P) x)
      exact (Localization.localRingHom_to_map P Q f hPQ x).symm
  have hS : Algebra.algebraMapSubmonoid A P.primeCompl = Q.primeCompl := by
    change P.primeCompl.map f = Q.primeCompl
    subst P
    exact Ideal.map_primeCompl_comap_of_surjective f hf Q
  letI : IsLocalization (Algebra.algebraMapSubmonoid A P.primeCompl)
      (Localization.AtPrime Q) := by
    rw [hS]
    infer_instance
  exact ((IsLocalizedModule.iso P.primeCompl
    (IsScalarTower.toAlgHom R A (Localization.AtPrime Q)).toLinearMap).extendScalarsOfIsLocalization
      P.primeCompl (Localization.AtPrime P)).toModuleIso

set_option backward.isDefEq.respectTransparency false in
/-- The comparison takes a numerator with denominator one to its actual image
in the source local ring. This fixes the underlying localization map. -/
theorem closedPrimeLocalizedModuleIso_hom_mk_one (f : R →+* A)
    (hf : Function.Surjective f) (P : Ideal R) [P.IsPrime]
    (Q : Ideal A) [Q.IsPrime] (hPQ : P = Q.comap f) (a : A) :
    (closedPrimeLocalizedModuleIso f hf P Q hPQ).hom
      (LocalizedModule.mk (a : specCoordinateModule f) 1) =
        algebraMap A (Localization.AtPrime Q) a := by
  let : Algebra R A := f.toAlgebra
  have hS : Algebra.algebraMapSubmonoid A P.primeCompl = Q.primeCompl := by
    change P.primeCompl.map f = Q.primeCompl
    subst P
    exact Ideal.map_primeCompl_comap_of_surjective f hf Q
  let : IsLocalization (Algebra.algebraMapSubmonoid A P.primeCompl)
      (Localization.AtPrime Q) := by
    rw [hS]
    infer_instance
  change IsLocalizedModule.iso P.primeCompl
    (IsScalarTower.toAlgHom R A (Localization.AtPrime Q)).toLinearMap
      (LocalizedModule.mk a 1) = _
  exact IsLocalizedModule.iso_mk_one _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The constructed map is linear for the literal localized scalar action. -/
theorem closedPrimeLocalizedModuleIso_hom_smul (f : R →+* A)
    (hf : Function.Surjective f) (P : Ideal R) [P.IsPrime]
    (Q : Ideal A) [Q.IsPrime] (hPQ : P = Q.comap f)
    (r : Localization.AtPrime P)
    (x : LocalizedModule P.primeCompl (specCoordinateModule f)) :
    ((closedPrimeLocalizedModuleIso f hf P Q hPQ).hom (r • x) :
      Localization.AtPrime Q) =
      Mul.mul (α := Localization.AtPrime Q) (Localization.localRingHom P Q f hPQ r)
        ((closedPrimeLocalizedModuleIso f hf P Q hPQ).hom x) :=
  (closedPrimeLocalizedModuleIso f hf P Q hPQ).hom.hom.map_smul r x

/-- The source localization bridge uses exactly `specSourceLocalMap`. -/
def closedSourceLocalizedModuleIso (f : R →+* A) (hf : Function.Surjective f)
    (p : PrimeSpectrum A) :
    ModuleCat.of (Localization.AtPrime (p.comap f).asIdeal)
      (LocalizedModule (p.comap f).asIdeal.primeCompl (specCoordinateModule f)) ≅
        specSourceLocalModule f p :=
  closedPrimeLocalizedModuleIso f hf (p.comap f).asIdeal p.asIdeal rfl

/-- The coefficient bridge uses the source's ambient prime and the specified
common-point equality, rather than an independently chosen scalar action. -/
def closedCoefficientLocalizedModuleIso (f : R →+* A) (p : PrimeSpectrum A)
    (g : R →+* B) (hg : Function.Surjective g) (q : PrimeSpectrum B)
    (hp : p.comap f = q.comap g) :
    ModuleCat.of (Localization.AtPrime (p.comap f).asIdeal)
      (LocalizedModule (p.comap f).asIdeal.primeCompl (specCoordinateModule g)) ≅
        specCoefficientLocalModule f p g q hp :=
  closedPrimeLocalizedModuleIso g hg (p.comap f).asIdeal q.asIdeal
    (congrArg PrimeSpectrum.asIdeal hp)

/-- Ambient-prime localization of actual coordinate Tor is actual Tor of the
source and coefficient local rings for two surjective coordinate maps. -/
def closedLocalizedCoordinateTorIso (f : R →+* A) (hf : Function.Surjective f)
    (p : PrimeSpectrum A) (g : R →+* B) (hg : Function.Surjective g)
    (q : PrimeSpectrum B) (hp : p.comap f = q.comap g) (n : ℕ) :
    ModuleCat.of (Localization.AtPrime (p.comap f).asIdeal)
      (LocalizedModule (p.comap f).asIdeal.primeCompl
        (((Tor (ModuleCat R) n).obj (specCoordinateModule g)).obj
          (specCoordinateModule f))) ≅
      ((Tor (ModuleCat (Localization.AtPrime (p.comap f).asIdeal)) n).obj
        (specCoefficientLocalModule f p g q hp)).obj (specSourceLocalModule f p) :=
  TorComparison.primeLocalizedTorIso (p.comap f).asIdeal
    (specCoordinateModule g) (specCoordinateModule f) n ≪≫
      ((Tor (ModuleCat (Localization.AtPrime (p.comap f).asIdeal)) n).mapIso
        (closedCoefficientLocalizedModuleIso f p g hg q hp)).app _ ≪≫
      ((Tor (ModuleCat (Localization.AtPrime (p.comap f).asIdeal)) n).obj
        (specCoefficientLocalModule f p g q hp)).mapIso
          (closedSourceLocalizedModuleIso f hf p)

/-- Actual stalk Tor for two affine closed subschemes is the localization of
actual coordinate Tor, restricted along the actual ambient stalk equivalence.
The coefficient is the first argument; no balancing or symmetry is assumed. -/
def closedSpecStalkTorIso (f : R →+* A) (hf : Function.Surjective f)
    (p : PrimeSpectrum A) (g : R →+* B) (hg : Function.Surjective g)
    (q : PrimeSpectrum B) (hp : p.comap f = q.comap g) (n : ℕ) :
    ((Tor (ModuleCat (ambientStalk (Spec.map (CommRingCat.ofHom f)) p)) n).obj
      (coefficientStalkModule (Spec.map (CommRingCat.ofHom f)) p
        (Spec.map (CommRingCat.ofHom g)) q hp)).obj
      (sourceStalkModule (Spec.map (CommRingCat.ofHom f)) p) ≅
      (ModuleCat.restrictScalars (specAmbientStalkEquiv f p).toRingHom).obj
        (ModuleCat.of (Localization.AtPrime (p.comap f).asIdeal)
          (LocalizedModule (p.comap f).asIdeal.primeCompl
            (((Tor (ModuleCat R) n).obj (specCoordinateModule g)).obj
              (specCoordinateModule f)))) :=
  specStalkTorIso f p g q hp n ≪≫
    (ModuleCat.restrictScalars (specAmbientStalkEquiv f p).toRingHom).mapIso
      (closedLocalizedCoordinateTorIso f hf p g hg q hp n).symm

end Motivic.Intersection
