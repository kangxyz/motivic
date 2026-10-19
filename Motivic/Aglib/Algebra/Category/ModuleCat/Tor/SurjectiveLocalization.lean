/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.FlatBaseChangeLocalization
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Localization and restriction along a surjective ring map

For any module over the quotient ring, localization at a prime commutes with
restriction of scalars to its inverse-image prime. The comparison is linear
for the literal localized ring map. No finiteness or module flatness is needed.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace ModuleCat.TorComparison

variable {R S : Type u} [CommRing R] [CommRing S]

set_option backward.isDefEq.respectTransparency false in
/-- Localization commutes with restriction along a surjection for arbitrary
modules, with the actual action of the literal local ring homomorphism. -/
def surjectivePrimeLocalizedModuleIso (f : R →+* S) (hf : Function.Surjective f)
    (P : Ideal R) [P.IsPrime] (Q : Ideal S) [Q.IsPrime] (hPQ : P = Q.comap f)
    (M : ModuleCat.{u} S) :
    ModuleCat.of (Localization.AtPrime P)
      (LocalizedModule P.primeCompl ((ModuleCat.restrictScalars f).obj M)) ≅
      (ModuleCat.restrictScalars (Localization.localRingHom P Q f hPQ)).obj
        (ModuleCat.of (Localization.AtPrime Q) (LocalizedModule Q.primeCompl M)) := by
  letI : Algebra R S := f.toAlgebra
  let L := (ModuleCat.restrictScalars f).obj M
  let T := (ModuleCat.restrictScalars (Localization.localRingHom P Q f hPQ)).obj
    (ModuleCat.of (Localization.AtPrime Q) (LocalizedModule Q.primeCompl M))
  letI : Module S L := inferInstanceAs (Module S M)
  letI : IsScalarTower R S L := ⟨fun r s x ↦ by
    change (f r * s) • x = f r • (s • x)
    exact mul_smul (f r) s x⟩
  letI : Module S T := inferInstanceAs (Module S (LocalizedModule Q.primeCompl M))
  letI : IsScalarTower S (Localization.AtPrime Q) T :=
    inferInstanceAs (IsScalarTower S (Localization.AtPrime Q)
      (LocalizedModule Q.primeCompl M))
  letI : Module R T := Module.compHom T f
  letI : IsScalarTower R S T := ⟨fun r s x ↦ by
    change (f r * s) • x = f r • (s • x)
    exact mul_smul (f r) s x⟩
  letI : IsScalarTower R (Localization.AtPrime P) T := ⟨fun r s x ↦ by
    change Localization.localRingHom P Q f hPQ (r • s) • x =
      f r • (Localization.localRingHom P Q f hPQ s • x)
    rw [Algebra.smul_def, map_mul, Localization.localRingHom_to_map, mul_smul,
      IsScalarTower.algebraMap_smul]⟩
  let l : L →ₗ[S] T := LocalizedModule.mkLinearMap Q.primeCompl M
  have hS : Algebra.algebraMapSubmonoid S P.primeCompl = Q.primeCompl := by
    change P.primeCompl.map f = Q.primeCompl
    subst P
    exact Ideal.map_primeCompl_comap_of_surjective f hf Q
  letI : IsLocalizedModule (Algebra.algebraMapSubmonoid S P.primeCompl) l := by
    rw [hS]
    exact localizedModuleIsLocalizedModule (M := M) Q.primeCompl
  letI : IsLocalizedModule P.primeCompl (l.restrictScalars R) :=
    IsLocalizedModule.restrictScalars P.primeCompl l
  exact ((IsLocalizedModule.iso P.primeCompl (l.restrictScalars R)).extendScalarsOfIsLocalization
    P.primeCompl (Localization.AtPrime P)).toModuleIso

set_option backward.isDefEq.respectTransparency false in
/-- The constructed localization map takes a numerator with denominator one
to the same numerator in the quotient-prime localization. -/
theorem surjectivePrimeLocalizedModuleIso_hom_mk_one (f : R →+* S)
    (hf : Function.Surjective f) (P : Ideal R) [P.IsPrime]
    (Q : Ideal S) [Q.IsPrime] (hPQ : P = Q.comap f) (M : ModuleCat.{u} S) (m : M) :
    (surjectivePrimeLocalizedModuleIso f hf P Q hPQ M).hom
      (LocalizedModule.mk (m : (ModuleCat.restrictScalars f).obj M) 1) =
        LocalizedModule.mk m 1 := by
  simp only [surjectivePrimeLocalizedModuleIso, LinearEquiv.toModuleIso,
    LinearEquiv.extendScalarsOfIsLocalization, LinearEquiv.coe_coe, LinearEquiv.coe_ofLinearMap,
    ModuleCat.hom_ofHom, LinearMap.extendScalarsOfIsLocalization_apply',
    IsLocalizedModule.iso_mk_one]
  rfl

/-- The map respects the literal localized quotient action. -/
theorem surjectivePrimeLocalizedModuleIso_hom_smul (f : R →+* S)
    (hf : Function.Surjective f) (P : Ideal R) [P.IsPrime]
    (Q : Ideal S) [Q.IsPrime] (hPQ : P = Q.comap f) (M : ModuleCat.{u} S)
    (r : Localization.AtPrime P)
    (x : LocalizedModule P.primeCompl ((ModuleCat.restrictScalars f).obj M)) :
    (surjectivePrimeLocalizedModuleIso f hf P Q hPQ M).hom (r • x) =
      Localization.localRingHom P Q f hPQ r •
        (surjectivePrimeLocalizedModuleIso f hf P Q hPQ M).hom x :=
  (surjectivePrimeLocalizedModuleIso f hf P Q hPQ M).hom.hom.map_smul r x

/-- Surjectivity survives localization at a prime and its inverse image,
for the literal local ring homomorphism used in restriction of scalars. -/
theorem localRingHom_surjective (f : R →+* S) (hf : Function.Surjective f)
    (P : Ideal R) [P.IsPrime] (Q : Ideal S) [Q.IsPrime] (hPQ : P = Q.comap f) :
    Function.Surjective (Localization.localRingHom P Q f hPQ) := by
  have hS : P.primeCompl.map f = Q.primeCompl := by
    subst P
    exact Ideal.map_primeCompl_comap_of_surjective f hf Q
  let : IsLocalization (P.primeCompl.map f) (Localization.AtPrime Q) := by
    rw [hS]
    infer_instance
  exact IsLocalization.map_surjective_of_surjective P.primeCompl
    (Localization.AtPrime P) (Localization.AtPrime Q) hf

end ModuleCat.TorComparison
