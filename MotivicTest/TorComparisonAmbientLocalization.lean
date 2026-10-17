/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.TorComparison.AmbientLocalization
public import Motivic.Algebra.Homology.TorComparison.AmbientMiddle
public import Mathlib.Data.ZMod.Basic

/-! # Consumers of actual surjective and ambient prime localization -/

@[expose] public section

noncomputable section

open CategoryTheory Motivic Motivic.TorComparison
open scoped TensorProduct Motivic.MiddleDiagonal

universe u

namespace MotivicTest.TorComparisonAmbientLocalization

/-- The restriction bridge applies to every module over every quotient. -/
def quotientModule (R : Type u) [CommRing R] (I : Ideal R)
    (q : Ideal (R ⧸ I)) [q.IsPrime] (M : ModuleCat.{u} (R ⧸ I)) :
    ModuleCat.of (Localization.AtPrime (q.comap (Ideal.Quotient.mk I)))
      (LocalizedModule (q.comap (Ideal.Quotient.mk I)).primeCompl
        ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj M)) ≅
      (ModuleCat.restrictScalars
        (Localization.localRingHom (q.comap (Ideal.Quotient.mk I)) q
          (Ideal.Quotient.mk I) rfl)).obj
        (ModuleCat.of (Localization.AtPrime q) (LocalizedModule q.primeCompl M)) :=
  surjectivePrimeLocalizedModuleIso (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    _ q rfl M

/-- Neither the base ring nor its quotient is required to be reduced. -/
def nonreducedModule (I : Ideal (ZMod 4)) (q : Ideal (ZMod 4 ⧸ I)) [q.IsPrime]
    (M : ModuleCat.{0} (ZMod 4 ⧸ I)) :=
  quotientModule (ZMod 4) I q M

/-- Surjectivity is proved for the exact localized quotient homomorphism. -/
theorem quotientLocalMap (R : Type u) [CommRing R] (I : Ideal R)
    (q : Ideal (R ⧸ I)) [q.IsPrime] :
    Function.Surjective (Localization.localRingHom
      (q.comap (Ideal.Quotient.mk I)) q (Ideal.Quotient.mk I) rfl) :=
  localRingHom_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective _ q rfl

/-- The map has an actual inverse on arbitrary localized quotient modules. -/
theorem quotientInverse (R : Type u) [CommRing R] (I : Ideal R)
    (q : Ideal (R ⧸ I)) [q.IsPrime] (M : ModuleCat.{u} (R ⧸ I))
    (x : LocalizedModule (q.comap (Ideal.Quotient.mk I)).primeCompl
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj M)) :
    (quotientModule R I q M).inv ((quotientModule R I q M).hom x) = x :=
  (quotientModule R I q M).toLinearEquiv.symm_apply_apply x

/-- Numerators are sent to their actual images, not an unspecified automorphism. -/
theorem quotientNumerator (R : Type u) [CommRing R] (I : Ideal R)
    (q : Ideal (R ⧸ I)) [q.IsPrime] (M : ModuleCat.{u} (R ⧸ I)) (m : M) :
    (quotientModule R I q M).hom
      (LocalizedModule.mk (m : (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj M) 1) =
        LocalizedModule.mk m 1 :=
  surjectivePrimeLocalizedModuleIso_hom_mk_one _ _ _ _ _ _ _

/-- The arbitrary-module quotient comparison uses the literal localized action. -/
theorem quotientScalar (R : Type u) [CommRing R] (I : Ideal R)
    (q : Ideal (R ⧸ I)) [q.IsPrime] (M : ModuleCat.{u} (R ⧸ I))
    (r : Localization.AtPrime (q.comap (Ideal.Quotient.mk I)))
    (x : LocalizedModule (q.comap (Ideal.Quotient.mk I)).primeCompl
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj M)) :
    (quotientModule R I q M).hom (r • x) =
      Localization.localRingHom (q.comap (Ideal.Quotient.mk I)) q
        (Ideal.Quotient.mk I) rfl r • (quotientModule R I q M).hom x :=
  surjectivePrimeLocalizedModuleIso_hom_smul _ _ _ _ _ _ _ _

variable (k A B C : Type u) [Field k] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]
  (q : Ideal (MiddleDiagonal.tripleRing k A B C)) [q.IsPrime]

/-- The literal middle diagonal discharges all factor-flatness assumptions
for arbitrary quotient support modules, at every prime and in every degree. -/
def middleQuotientSupports (I : Ideal (A ⊗[k] B)) (J : Ideal (B ⊗[k] C)) (n : ℕ) :=
  primeLocalizedAmbientTorIso (MiddleDiagonal.quotientMap k A B C).toRingHom
    (MiddleDiagonal.quotientMap_surjective k A B C)
    (by rw [ambientMiddle_leftMap]; exact AffineMiddle.leftMap_flat k A B C)
    (by rw [ambientMiddle_rightMap]; exact AffineMiddle.rightMap_flat k A B C)
    (q.comap (MiddleDiagonal.quotientMap k A B C).toRingHom) q rfl
    (ModuleCat.of (A ⊗[k] B) ((A ⊗[k] B) ⧸ I))
    (ModuleCat.of (B ⊗[k] C) ((B ⊗[k] C) ⧸ J)) n

/-- The same middle-diagonal comparison can be computed entirely with actual
Tor over the two local rings, without asserting quotient flatness. -/
def middleLocalTor (M : ModuleCat.{u} (A ⊗[k] B))
    (N : ModuleCat.{u} (B ⊗[k] C)) (n : ℕ) :=
  ambientPrimeTorIso (MiddleDiagonal.quotientMap k A B C).toRingHom
    (MiddleDiagonal.quotientMap_surjective k A B C)
    (by rw [ambientMiddle_leftMap]; exact AffineMiddle.leftMap_flat k A B C)
    (by rw [ambientMiddle_rightMap]; exact AffineMiddle.rightMap_flat k A B C)
    (q.comap (MiddleDiagonal.quotientMap k A B C).toRingHom) q rfl M N n

end MotivicTest.TorComparisonAmbientLocalization
