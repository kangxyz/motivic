/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.TorComparison.RingEquiv
public import Motivic.AlgebraicGeometry.Intersection.StalkModules
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Actual affine intersection stalk Tor as localized-ring Tor

The source and coefficient stalks of two actual affine scheme maps are
identified with their prime localizations. The same ambient localization
acts through the literal localized ring homomorphisms, including the equal
ambient-point transport for the coefficient. Ring-equivalence invariance of
actual categorical Tor then gives an all-degree comparison. No product stalk
is replaced by a tensor product of stalks, and no Tor symmetry is assumed.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic.Intersection

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]

/-- Equal affine points induce the canonical identity-map localization morphism. -/
theorem spec_stalkCongr_stalkIso (p q : PrimeSpectrum R) (h : p = q) :
    ((Spec (.of R)).presheaf.stalkCongr (.of_eq h)).hom ≫
        (Spec.stalkIso (.of R) q).hom =
      (Spec.stalkIso (.of R) p).hom ≫ CommRingCat.ofHom
        (Localization.localRingHom p.asIdeal q.asIdeal (RingHom.id R)
          (by subst q; exact (Ideal.comap_id _).symm)) := by
  subst q
  rw [Localization.localRingHom_id]
  change (Spec (.of R)).presheaf.stalkSpecializes (specializes_refl p) ≫
    (Spec.stalkIso (.of R) p).hom = (Spec.stalkIso (.of R) p).hom ≫ 𝟙 _
  erw [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]

/-- The actual affine ambient stalk is the localization at the image prime. -/
def specAmbientStalkEquiv (f : R →+* A) (p : PrimeSpectrum A) :
    ambientStalk (Spec.map (CommRingCat.ofHom f)) p ≃+*
      Localization.AtPrime (p.comap f).asIdeal :=
  (Spec.stalkIso (.of R) (p.comap f)).commRingCatIsoToRingEquiv

/-- The literal localized scalar map associated to an affine source point. -/
def specSourceLocalMap (f : R →+* A) (p : PrimeSpectrum A) :
    Localization.AtPrime (p.comap f).asIdeal →+* Localization.AtPrime p.asIdeal :=
  Localization.localRingHom (p.comap f).asIdeal p.asIdeal f rfl

/-- The affine source module has its actual localized scalar action. -/
def specSourceLocalModule (f : R →+* A) (p : PrimeSpectrum A) :
    ModuleCat (Localization.AtPrime (p.comap f).asIdeal) :=
  (ModuleCat.restrictScalars (specSourceLocalMap f p)).obj
    (ModuleCat.of (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal))

/-- The actual source stalk module is identified by the literal affine stalk square. -/
def specSourceStalkModuleIso (f : R →+* A) (p : PrimeSpectrum A) :
    sourceStalkModule (Spec.map (CommRingCat.ofHom f)) p ≅
      (ModuleCat.restrictScalars (specAmbientStalkEquiv f p).toRingHom).obj
        (specSourceLocalModule f p) := by
  apply TorComparison.ringModuleIso (specAmbientStalkEquiv f p)
    (Spec.stalkIso (.of A) p).commRingCatIsoToRingEquiv
    ((Spec.map (CommRingCat.ofHom f)).stalkMap p).hom (specSourceLocalMap f p)
  intro r
  exact (ConcreteCategory.congr_hom
    (Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom f) p).hom.w r).symm

variable (f : R →+* A) (p : PrimeSpectrum A) (g : R →+* B) (q : PrimeSpectrum B)
  (hp : p.comap f = q.comap g)

/-- The coefficient scalar map uses the same ambient prime localization. -/
def specCoefficientLocalMap :
    Localization.AtPrime (p.comap f).asIdeal →+* Localization.AtPrime q.asIdeal :=
  Localization.localRingHom (p.comap f).asIdeal q.asIdeal g (congrArg PrimeSpectrum.asIdeal hp)

/-- The actual localized coefficient module with its specified common ambient action. -/
def specCoefficientLocalModule : ModuleCat (Localization.AtPrime (p.comap f).asIdeal) :=
  (ModuleCat.restrictScalars (specCoefficientLocalMap f p g q hp)).obj
    (ModuleCat.of (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal))

/-- The canonical localization transport composes to the direct coefficient local map. -/
theorem specCoefficientLocalMap_eq_comp :
    specCoefficientLocalMap f p g q hp =
      (specSourceLocalMap g q).comp
        (Localization.localRingHom (p.comap f).asIdeal (q.comap g).asIdeal (RingHom.id R)
          ((congrArg PrimeSpectrum.asIdeal hp).trans (Ideal.comap_id _).symm)) := by
  simpa only [specCoefficientLocalMap, specSourceLocalMap, RingHom.comp_id] using
    (Localization.localRingHom_comp (p.comap f).asIdeal (q.comap g).asIdeal q.asIdeal
      (RingHom.id R)
      ((congrArg PrimeSpectrum.asIdeal hp).trans (Ideal.comap_id _).symm) g rfl)

/-- The actual coefficient stalk square includes, and respects, the common-point transport. -/
theorem spec_coefficientStalkMap_commutes
    (r : ambientStalk (Spec.map (CommRingCat.ofHom f)) p) :
    (Spec.stalkIso (.of B) q).hom
        (coefficientStalkMap (Spec.map (CommRingCat.ofHom f)) p
          (Spec.map (CommRingCat.ofHom g)) q hp r) =
      specCoefficientLocalMap f p g q hp (specAmbientStalkEquiv f p r) := by
  rw [specCoefficientLocalMap_eq_comp]
  have hs := ConcreteCategory.congr_hom
    (Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom g) q).hom.w
    (((Spec (.of R)).presheaf.stalkCongr (.of_eq hp)).hom r)
  have hp' := ConcreteCategory.congr_hom
    (spec_stalkCongr_stalkIso (p.comap f) (q.comap g) hp) r
  change _ = specSourceLocalMap g q _
  exact hs.symm.trans (congrArg (specSourceLocalMap g q) hp')

/-- The actual coefficient module is the localized module with its literal scalar action. -/
def specCoefficientStalkModuleIso :
    coefficientStalkModule (Spec.map (CommRingCat.ofHom f)) p
      (Spec.map (CommRingCat.ofHom g)) q hp ≅
      (ModuleCat.restrictScalars (specAmbientStalkEquiv f p).toRingHom).obj
        (specCoefficientLocalModule f p g q hp) :=
  TorComparison.ringModuleIso (specAmbientStalkEquiv f p)
    (Spec.stalkIso (.of B) q).commRingCatIsoToRingEquiv
    (coefficientStalkMap (Spec.map (CommRingCat.ofHom f)) p
      (Spec.map (CommRingCat.ofHom g)) q hp).hom
    (specCoefficientLocalMap f p g q hp) (spec_coefficientStalkMap_commutes f p g q hp)

/-- Actual Tor of the two affine source stalks is actual Tor of the localized
coordinate rings, with all scalar maps and the common ambient point identified. -/
def specStalkTorIso (n : ℕ) :
    ((Tor (ModuleCat (ambientStalk (Spec.map (CommRingCat.ofHom f)) p)) n).obj
      (coefficientStalkModule (Spec.map (CommRingCat.ofHom f)) p
      (Spec.map (CommRingCat.ofHom g)) q hp)).obj
        (sourceStalkModule (Spec.map (CommRingCat.ofHom f)) p) ≅
      (ModuleCat.restrictScalars (specAmbientStalkEquiv f p).toRingHom).obj
        (((Tor (ModuleCat (Localization.AtPrime (p.comap f).asIdeal)) n).obj
          (specCoefficientLocalModule f p g q hp)).obj (specSourceLocalModule f p)) :=
  TorComparison.torIsoOfScalarIso (specAmbientStalkEquiv f p) _ _ _ _
    (specCoefficientStalkModuleIso f p g q hp) (specSourceStalkModuleIso f p) n

end Motivic.Intersection
