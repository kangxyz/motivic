/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Intersection.SpecTor
public import Mathlib.Data.ZMod.Basic

/-! # Consumers of actual affine-stalk Tor and scalar transport -/

@[expose] public section

noncomputable section

open _root_.ModuleCat.TorComparison (ringEquivRestrictTorIso ringModuleIso)
open CategoryTheory AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Intersection

universe u

namespace MotivicTest.SpecStalkTor

variable (R S : Type u) [CommRing R] [CommRing S]

/-- Swapping two factors of a genuinely possibly disconnected coefficient ring
transports actual Tor with both literal restricted module actions. -/
def productSwapTor (M N : ModuleCat.{u} (S × R)) (n : ℕ) :
    ((Tor (ModuleCat (R × S)) n).obj
      ((ModuleCat.restrictScalars (RingEquiv.prodComm : R × S ≃+* S × R).toRingHom).obj M)).obj
        ((ModuleCat.restrictScalars (RingEquiv.prodComm : R × S ≃+* S × R).toRingHom).obj N) ≅
      (ModuleCat.restrictScalars (RingEquiv.prodComm : R × S ≃+* S × R).toRingHom).obj
        (((Tor (ModuleCat (S × R)) n).obj M).obj N) :=
  ringEquivRestrictTorIso (RingEquiv.prodComm : R × S ≃+* S × R) M N n

variable {R S}

/-- A real coordinate-ring change has its specified composed scalar action. -/
def changeCoordinateRingModule {A : Type u} [CommRing A] (e : R ≃+* S) (f : R →+* A) :
    (ModuleCat.restrictScalars f).obj (ModuleCat.of A A) ≅
      (ModuleCat.restrictScalars e.toRingHom).obj
        ((ModuleCat.restrictScalars (f.comp e.symm.toRingHom)).obj (ModuleCat.of A A)) :=
  ringModuleIso e (RingEquiv.refl A) f (f.comp e.symm.toRingHom)
    (fun r ↦ by simp)

/-- Self-intersection of an actual affine closed subscheme uses its complete
localized quotient ring, without assuming the intersection transverse. -/
def quotientSelfIntersectionTor (I : Ideal R) (p : PrimeSpectrum (R ⧸ I)) (n : ℕ) :
    ((Tor (ModuleCat (ambientStalk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) p))
      n).obj
      (coefficientStalkModule (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) p
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) p rfl)).obj
      (sourceStalkModule (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) p) ≅
      (ModuleCat.restrictScalars (specAmbientStalkEquiv (Ideal.Quotient.mk I) p).toRingHom).obj
        (((Tor (ModuleCat (Localization.AtPrime (p.comap (Ideal.Quotient.mk I)).asIdeal)) n).obj
          (specCoefficientLocalModule (Ideal.Quotient.mk I) p (Ideal.Quotient.mk I) p rfl)).obj
          (specSourceLocalModule (Ideal.Quotient.mk I) p)) :=
  specStalkTorIso (Ideal.Quotient.mk I) p (Ideal.Quotient.mk I) p rfl n

/-- The actual scalar map for two affine quotient supports is identified elementwise. -/
theorem quotient_coefficient_scalars (I J : Ideal R)
    (p : PrimeSpectrum (R ⧸ I)) (q : PrimeSpectrum (R ⧸ J))
    (hp : p.comap (Ideal.Quotient.mk I) = q.comap (Ideal.Quotient.mk J))
    (r : ambientStalk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) p) :
    (Spec.stalkIso (.of (R ⧸ J)) q).hom
      (coefficientStalkMap (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) p
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) q hp r) =
      specCoefficientLocalMap (Ideal.Quotient.mk I) p (Ideal.Quotient.mk J) q hp
        (specAmbientStalkEquiv (Ideal.Quotient.mk I) p r) :=
  spec_coefficientStalkMap_commutes (Ideal.Quotient.mk I) p (Ideal.Quotient.mk J) q hp r

/-- A nonreduced ambient ring is permitted in the complete all-degree affine comparison. -/
def nonreducedSpecTor (p : PrimeSpectrum (ZMod 4)) (n : ℕ) :
    ((Tor (ModuleCat (ambientStalk
      (Spec.map (CommRingCat.ofHom (RingHom.id (ZMod 4)))) p)) n).obj
      (coefficientStalkModule (Spec.map (CommRingCat.ofHom (RingHom.id (ZMod 4)))) p
        (Spec.map (CommRingCat.ofHom (RingHom.id (ZMod 4)))) p rfl)).obj
      (sourceStalkModule (Spec.map (CommRingCat.ofHom (RingHom.id (ZMod 4)))) p) ≅
      (ModuleCat.restrictScalars (specAmbientStalkEquiv (RingHom.id (ZMod 4)) p).toRingHom).obj
        (((Tor (ModuleCat
          (Localization.AtPrime (p.comap (RingHom.id (ZMod 4))).asIdeal)) n).obj
          (specCoefficientLocalModule (RingHom.id (ZMod 4)) p (RingHom.id (ZMod 4)) p rfl)).obj
          (specSourceLocalModule (RingHom.id (ZMod 4)) p)) :=
  specStalkTorIso (RingHom.id (ZMod 4)) p (RingHom.id (ZMod 4)) p rfl n

end MotivicTest.SpecStalkTor
