/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Intersection.ClosedSpecTor
public import Mathlib.Data.ZMod.Basic

/-!
# Consumers of the closed affine coordinate-to-stalk Tor bridge

These examples use actual quotient maps, the projection of a disconnected
ring, two possibly different support ideals, and a nonreduced ambient ring.
No target comparison or regularity assumption is supplied.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Intersection

universe u

namespace MotivicTest.ClosedSpecStalkTor

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Ambient localization of a quotient module is its actual source local ring. -/
def quotientLocalizedModule (I : Ideal R) (p : PrimeSpectrum (R ⧸ I)) :
    ModuleCat.of (Localization.AtPrime (p.comap (Ideal.Quotient.mk I)).asIdeal)
      (LocalizedModule (p.comap (Ideal.Quotient.mk I)).asIdeal.primeCompl
        (specCoordinateModule (Ideal.Quotient.mk I))) ≅
      specSourceLocalModule (Ideal.Quotient.mk I) p :=
  closedSourceLocalizedModuleIso (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective p

/-- The projection of a product ring is surjective even when the source
spectrum is disconnected; the comparison keeps its actual scalar map. -/
def productProjectionLocalizedModule (p : PrimeSpectrum R) :
    ModuleCat.of (Localization.AtPrime (p.comap (RingHom.fst R S)).asIdeal)
      (LocalizedModule (p.comap (RingHom.fst R S)).asIdeal.primeCompl
        (specCoordinateModule (RingHom.fst R S))) ≅
      specSourceLocalModule (RingHom.fst R S) p :=
  closedSourceLocalizedModuleIso (RingHom.fst R S) (fun r ↦ ⟨(r, 0), rfl⟩) p

/-- Two arbitrary quotient supports have actual all-degree localized
coordinate Tor, with the coefficient first and the source resolved second. -/
def quotientPairStalkTor (I J : Ideal R)
    (p : PrimeSpectrum (R ⧸ I)) (q : PrimeSpectrum (R ⧸ J))
    (hp : p.comap (Ideal.Quotient.mk I) = q.comap (Ideal.Quotient.mk J)) (n : ℕ) :
    ((Tor (ModuleCat (ambientStalk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) p))
      n).obj
      (coefficientStalkModule (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) p
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) q hp)).obj
      (sourceStalkModule (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) p) ≅
      (ModuleCat.restrictScalars (specAmbientStalkEquiv (Ideal.Quotient.mk I) p).toRingHom).obj
        (ModuleCat.of (Localization.AtPrime (p.comap (Ideal.Quotient.mk I)).asIdeal)
          (LocalizedModule (p.comap (Ideal.Quotient.mk I)).asIdeal.primeCompl
            (((Tor (ModuleCat R) n).obj (specCoordinateModule (Ideal.Quotient.mk J))).obj
              (specCoordinateModule (Ideal.Quotient.mk I))))) :=
  closedSpecStalkTorIso (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective p
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective q hp n

/-- The coefficient bridge at a shared ambient point has the actual quotient
localization map on ordinary numerators. -/
theorem quotient_coefficient_numerator (I J : Ideal R)
    (p : PrimeSpectrum (R ⧸ I)) (q : PrimeSpectrum (R ⧸ J))
    (hp : p.comap (Ideal.Quotient.mk I) = q.comap (Ideal.Quotient.mk J)) (b : R ⧸ J) :
    (closedCoefficientLocalizedModuleIso (Ideal.Quotient.mk I) p (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective q hp).hom
      (LocalizedModule.mk (b : specCoordinateModule (Ideal.Quotient.mk J)) 1) =
      algebraMap (R ⧸ J) (Localization.AtPrime q.asIdeal) b :=
  closedPrimeLocalizedModuleIso_hom_mk_one (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective _ _ _ b

/-- Shared-point coefficient scalars are exactly the direct local ring map,
including the equality transport from the other support's ambient prime. -/
theorem quotient_coefficient_scalars (I J : Ideal R)
    (p : PrimeSpectrum (R ⧸ I)) (q : PrimeSpectrum (R ⧸ J))
    (hp : p.comap (Ideal.Quotient.mk I) = q.comap (Ideal.Quotient.mk J))
    (r : Localization.AtPrime (p.comap (Ideal.Quotient.mk I)).asIdeal)
    (x : LocalizedModule (p.comap (Ideal.Quotient.mk I)).asIdeal.primeCompl
      (specCoordinateModule (Ideal.Quotient.mk J))) :
    ((closedCoefficientLocalizedModuleIso (Ideal.Quotient.mk I) p (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective q hp).hom (r • x) : Localization.AtPrime q.asIdeal) =
      Mul.mul (α := Localization.AtPrime q.asIdeal)
        (specCoefficientLocalMap (Ideal.Quotient.mk I) p (Ideal.Quotient.mk J) q hp r)
        ((closedCoefficientLocalizedModuleIso (Ideal.Quotient.mk I) p (Ideal.Quotient.mk J)
          Ideal.Quotient.mk_surjective q hp).hom x) :=
  closedPrimeLocalizedModuleIso_hom_smul (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective _ _ _ r x

/-- A nonreduced ambient ring and its nontrivial quotient support require
neither regularity nor higher-Tor vanishing for the actual comparison. -/
def nonreducedQuotientSelfIntersectionTor
    (p : PrimeSpectrum (ZMod 4 ⧸ Ideal.span ({2} : Set (ZMod 4)))) (n : ℕ) :
    let I : Ideal (ZMod 4) := Ideal.span {2}
    ((Tor (ModuleCat (ambientStalk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) p))
      n).obj
      (coefficientStalkModule (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) p
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) p rfl)).obj
      (sourceStalkModule (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) p) ≅
      (ModuleCat.restrictScalars (specAmbientStalkEquiv (Ideal.Quotient.mk I) p).toRingHom).obj
        (ModuleCat.of (Localization.AtPrime (p.comap (Ideal.Quotient.mk I)).asIdeal)
          (LocalizedModule (p.comap (Ideal.Quotient.mk I)).asIdeal.primeCompl
            (((Tor (ModuleCat (ZMod 4)) n).obj (specCoordinateModule (Ideal.Quotient.mk I))).obj
              (specCoordinateModule (Ideal.Quotient.mk I))))) :=
  quotientPairStalkTor _ _ p p rfl n

end MotivicTest.ClosedSpecStalkTor
