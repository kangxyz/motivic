/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Intersection.ClosedSpecTor
public import Motivic.Algebra.Homology.TorComparison.SurjectiveLocalization
public import Motivic.Algebra.Homology.TorComparison.AmbientLength

/-!
# Actual closed affine Tor comparison transport

A constructed coordinate-module isomorphism localizes through a surjective
coordinate map and then transports to the actual scheme stalks. Both closed
stalk bridges and the literal scalar square are constructed here. Applications
must supply their independently proved coordinate comparison; this file does
not assert arbitrary change of rings for Tor.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic.Intersection

/-- The actual affine stalk square identifies the two iterated restrictions
of an arbitrary module over the source prime localization. -/
def specStalkRestrictionSquareIso {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum S)
    (M : ModuleCat.{u} (Localization.AtPrime p.asIdeal)) :
    (ModuleCat.restrictScalars (specAmbientStalkEquiv f p).toRingHom).obj
      ((ModuleCat.restrictScalars (specSourceLocalMap f p)).obj M) ≅
    (ModuleCat.restrictScalars ((Spec.map (CommRingCat.ofHom f)).stalkMap p).hom).obj
      ((ModuleCat.restrictScalars
        (Spec.stalkIso (.of S) p).commRingCatIsoToRingEquiv.toRingHom).obj M) := by
  have h : (specSourceLocalMap f p).comp (specAmbientStalkEquiv f p).toRingHom =
      (Spec.stalkIso (.of S) p).commRingCatIsoToRingEquiv.toRingHom.comp
        ((Spec.map (CommRingCat.ofHom f)).stalkMap p).hom := by
    ext x
    exact ConcreteCategory.congr_hom
      (Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom f) p).hom.w x
  exact (ModuleCat.restrictScalarsComp _ _).symm.app M ≪≫
    (ModuleCat.restrictScalarsCongr h).app M ≪≫
    (ModuleCat.restrictScalarsComp _ _).app M

/-- Surjectivity of an affine closed coordinate map gives surjectivity of the
literal scheme stalk map, through its actual localization square. -/
theorem specStalkMap_surjective {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (p : PrimeSpectrum S) :
    Function.Surjective ((Spec.map (CommRingCat.ofHom f)).stalkMap p).hom := by
  let e := (Spec.stalkIso (.of S) p).commRingCatIsoToRingEquiv
  intro x
  obtain ⟨a, ha⟩ := TorComparison.localRingHom_surjective f hf
    (p.comap f).asIdeal p.asIdeal rfl (e x)
  obtain ⟨b, rfl⟩ := (specAmbientStalkEquiv f p).surjective a
  refine ⟨b, e.injective ?_⟩
  exact (ConcreteCategory.congr_hom
    (Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom f) p).hom.w b).symm.trans ha

/-- Actual coordinate Tor for two specified closed maps, coefficient first. -/
def closedCoordinateTor {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : R →+* B) (n : ℕ) : ModuleCat.{u} R :=
  ((Tor (ModuleCat R) n).obj (specCoordinateModule f)).obj (specCoordinateModule g)

/-- Actual scheme-stalk Tor for two closed affine coordinate maps, coefficient first. -/
def closedStalkTor {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (p : PrimeSpectrum A) (g : R →+* B) (q : PrimeSpectrum B)
    (hp : p.comap f = q.comap g) (n : ℕ) :
    ModuleCat.{u} (ambientStalk (Spec.map (CommRingCat.ofHom f)) p) :=
  ((Tor (ModuleCat (ambientStalk (Spec.map (CommRingCat.ofHom f)) p)) n).obj
    (coefficientStalkModule (Spec.map (CommRingCat.ofHom f)) p
      (Spec.map (CommRingCat.ofHom g)) q hp)).obj
        (sourceStalkModule (Spec.map (CommRingCat.ofHom f)) p)

/-- Localization of a bundled module at the specified prime, with its actual local action. -/
def primeLocalizedModule {R : Type u} [CommRing R]
    (p : Ideal R) [p.IsPrime] (M : ModuleCat.{u} R) :
    ModuleCat.{u} (Localization.AtPrime p) :=
  ModuleCat.of (Localization.AtPrime p) (LocalizedModule p.primeCompl M)

/-- Localizing a constructed module comparison along a surjective quotient
uses the literal localized scalar map. -/
def closedLocalizedComparisonIso {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (q : PrimeSpectrum S)
    (M : ModuleCat.{u} R) (N : ModuleCat.{u} S)
    (e : M ≅ (ModuleCat.restrictScalars f).obj N) :
    primeLocalizedModule (q.comap f).asIdeal M ≅
      (ModuleCat.restrictScalars (specSourceLocalMap f q)).obj
        (primeLocalizedModule q.asIdeal N) :=
  TorComparison.localizedModuleExtendScalarsIso (q.comap f).asIdeal.primeCompl M ≪≫
    (ModuleCat.extendScalars
      (algebraMap R (Localization.AtPrime (q.comap f).asIdeal))).mapIso e ≪≫
    (TorComparison.localizedModuleExtendScalarsIso (q.comap f).asIdeal.primeCompl
      ((ModuleCat.restrictScalars f).obj N)).symm ≪≫
    TorComparison.surjectivePrimeLocalizedModuleIso f hf (q.comap f).asIdeal q.asIdeal rfl N

/-- A genuine coordinate Tor comparison gives the corresponding actual closed
stalk comparison. This is transport of the supplied construction, not an
assertion of an arbitrary ambient Tor comparison. -/
def closedStalkComparisonIso {P Q T L R : Type u}
    [CommRing P] [CommRing Q] [CommRing T] [CommRing L] [CommRing R]
    (μ : P →+* Q) (hμ : Function.Surjective μ)
    (σ : P →+* T) (hσ : Function.Surjective σ)
    (a : Q →+* L) (ha : Function.Surjective a)
    (b : Q →+* R) (hb : Function.Surjective b)
    (l : PrimeSpectrum L) (r : PrimeSpectrum R) (t : PrimeSpectrum T)
    (hq : r.comap b = l.comap a) (hp : (r.comap b).comap μ = t.comap σ) (n : ℕ)
    (e : closedCoordinateTor σ μ n ≅
      (ModuleCat.restrictScalars μ).obj (closedCoordinateTor a b n)) :
    closedStalkTor μ (r.comap b) σ t hp n ≅
      (ModuleCat.restrictScalars ((Spec.map (CommRingCat.ofHom μ)).stalkMap (r.comap b)).hom).obj
        (closedStalkTor b r a l hq n) :=
  closedSpecStalkTorIso μ hμ (r.comap b) σ hσ t hp n ≪≫
    (ModuleCat.restrictScalars (specAmbientStalkEquiv μ (r.comap b)).toRingHom).mapIso
      (closedLocalizedComparisonIso μ hμ (r.comap b)
        (closedCoordinateTor σ μ n) (closedCoordinateTor a b n) e) ≪≫
    specStalkRestrictionSquareIso μ (r.comap b)
      (primeLocalizedModule (r.comap b).asIdeal (closedCoordinateTor a b n)) ≪≫
    (ModuleCat.restrictScalars
      ((Spec.map (CommRingCat.ofHom μ)).stalkMap (r.comap b)).hom).mapIso
        (closedSpecStalkTorIso b hb r a ha l hq n).symm

/-- The actual local lengths agree after a constructed closed-stalk comparison.
Surjectivity is used on the literal geometric stalk map. -/
theorem closedStalkComparison_length {P Q T L R : Type u}
    [CommRing P] [CommRing Q] [CommRing T] [CommRing L] [CommRing R]
    (μ : P →+* Q) (hμ : Function.Surjective μ)
    (σ : P →+* T) (hσ : Function.Surjective σ)
    (a : Q →+* L) (ha : Function.Surjective a)
    (b : Q →+* R) (hb : Function.Surjective b)
    (l : PrimeSpectrum L) (r : PrimeSpectrum R) (t : PrimeSpectrum T)
    (hq : r.comap b = l.comap a) (hp : (r.comap b).comap μ = t.comap σ) (n : ℕ)
    (e : closedCoordinateTor σ μ n ≅
      (ModuleCat.restrictScalars μ).obj (closedCoordinateTor a b n)) :
    Module.length (ambientStalk (Spec.map (CommRingCat.ofHom μ)) (r.comap b))
      (closedStalkTor μ (r.comap b) σ t hp n) =
    Module.length (ambientStalk (Spec.map (CommRingCat.ofHom b)) r)
      (closedStalkTor b r a l hq n) :=
  (closedStalkComparisonIso μ hμ σ hσ a ha b hb l r t hq hp n e).toLinearEquiv.length_eq.trans
    (TorComparison.length_restrictScalars_of_surjective _
      (specStalkMap_surjective μ hμ (r.comap b)) _)

end Motivic.Intersection
