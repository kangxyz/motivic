/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.FlatBaseChange
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Actual module localization commutes with categorical Tor

The flat base-change theorem specializes to localization at any submonoid.
The final result uses literal `LocalizedModule` modules on both sides,
with their actual `Localization p` actions, rather than leaving the ordinary
module-localization identification as a hypothesis. Identifying these modules
with particular scheme stalks is a separate geometric step.
-/

@[expose] public section

open CategoryTheory

universe u

namespace ModuleCat.TorComparison

variable {R : Type u} [CommRing R]

set_option backward.isDefEq.respectTransparency false in
/-- Ordinary localization is the scalar extension along the canonical
localization map, including its full localized-ring module action. -/
noncomputable def localizedModuleExtendScalarsIso (p : Submonoid R)
    (M : ModuleCat.{u} R) :
    ModuleCat.of (Localization p) (LocalizedModule p M) ≅
      (ModuleCat.extendScalars (algebraMap R (Localization p))).obj M := by
  let A := (ModuleCat.restrictScalars (algebraMap R (Localization p))).obj
    (ModuleCat.of (Localization p) (Localization p))
  letI : IsScalarTower R (Localization p) A := ⟨fun r s t ↦ by
    change (r • s) • t = algebraMap R (Localization p) r • (s • t)
    rw [Algebra.smul_def, mul_smul]⟩
  let e : Localization p ≃ₗ[Localization p] A := LinearEquiv.refl _ _
  exact (LocalizedModule.equivTensorProduct p M).toModuleIso ≪≫
    (TensorProduct.AlgebraTensorModule.congr e (LinearEquiv.refl R M)).toModuleIso

/-- Localization of actual Tor is actual Tor of the localized modules in every
degree. This constructs an isomorphism of `Localization p`-modules. -/
noncomputable def localizedTorIso (p : Submonoid R) (M N : ModuleCat.{u} R) (n : ℕ) :
    ModuleCat.of (Localization p)
        (LocalizedModule p (((Tor (ModuleCat R) n).obj M).obj N)) ≅
      ((Tor (ModuleCat (Localization p)) n).obj
        (ModuleCat.of (Localization p) (LocalizedModule p M))).obj
        (ModuleCat.of (Localization p) (LocalizedModule p N)) :=
  localizedModuleExtendScalarsIso p _ ≪≫
    flatBaseChangeTorIso (algebraMap R (Localization p))
      (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat (Localization p) p)) M N n ≪≫
    ((Tor (ModuleCat (Localization p)) n).mapIso
      (localizedModuleExtendScalarsIso p M).symm).app _ ≪≫
    ((Tor (ModuleCat (Localization p)) n).obj
      (ModuleCat.of (Localization p) (LocalizedModule p M))).mapIso
      (localizedModuleExtendScalarsIso p N).symm

/-- The prime-local version retains actual localized modules and scalar
structures, without replacing a product stalk by a tensor of stalks. -/
noncomputable def primeLocalizedTorIso (P : Ideal R) [P.IsPrime]
    (M N : ModuleCat.{u} R) (n : ℕ) :
    ModuleCat.of (Localization.AtPrime P)
        (LocalizedModule P.primeCompl (((Tor (ModuleCat R) n).obj M).obj N)) ≅
      ((Tor (ModuleCat (Localization.AtPrime P)) n).obj
        (ModuleCat.of (Localization.AtPrime P) (LocalizedModule P.primeCompl M))).obj
        (ModuleCat.of (Localization.AtPrime P) (LocalizedModule P.primeCompl N)) :=
  localizedTorIso P.primeCompl M N n

end ModuleCat.TorComparison
