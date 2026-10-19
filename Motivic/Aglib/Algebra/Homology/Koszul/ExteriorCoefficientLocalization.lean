/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.Koszul.ExteriorCoefficientComparison
public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.SurjectiveLocalization
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Localization of literal exterior Koszul homology

Localization of scalar extension is scalar extension along the actual local
ring map from the source-prime localization. The literal exterior homology
comparison then localizes through the quotient map on the additional factor.
These comparisons retain the ambient local-ring action in every degree and
do not assume genericity or a closed-fiber multiplicity formula.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory
open scoped TensorProduct ChangeOfRings

namespace ChainComplex.Koszul

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The literal localized scalar map satisfies the localization square. -/
theorem primeLocalRingHom_square (f : R →+* S) (P : Ideal R) [P.IsPrime]
    (Q : Ideal S) [Q.IsPrime] (hPQ : P = Q.comap f) :
    (Localization.localRingHom P Q f hPQ).comp (algebraMap R (Localization.AtPrime P)) =
      (algebraMap S (Localization.AtPrime Q)).comp f := by
  ext x
  exact Localization.localRingHom_to_map P Q f hPQ x

/-- Actual localization of scalar extension cancels to extension of the
source localization along the literal local ring map. No flatness is needed. -/
def primeLocalizedExtendScalarsIso (f : R →+* S) (P : Ideal R) [P.IsPrime]
    (Q : Ideal S) [Q.IsPrime] (hPQ : P = Q.comap f) (M : ModuleCat R) :
    ModuleCat.of (Localization.AtPrime Q)
        (LocalizedModule Q.primeCompl ((ModuleCat.extendScalars f).obj M)) ≅
      (ModuleCat.extendScalars (Localization.localRingHom P Q f hPQ)).obj
        (ModuleCat.of (Localization.AtPrime P) (LocalizedModule P.primeCompl M)) :=
  _root_.ModuleCat.TorComparison.localizedModuleExtendScalarsIso Q.primeCompl _ ≪≫
    (ModuleCat.extendScalarsComp f (algebraMap S (Localization.AtPrime Q))).symm.app M ≪≫
    eqToIso (congrArg (fun g : R →+* Localization.AtPrime Q =>
      (ModuleCat.extendScalars g).obj M) (primeLocalRingHom_square f P Q hPQ).symm) ≪≫
    (ModuleCat.extendScalarsComp (algebraMap R (Localization.AtPrime P))
      (Localization.localRingHom P Q f hPQ)).app M ≪≫
    (ModuleCat.extendScalars (Localization.localRingHom P Q f hPQ)).mapIso
      (_root_.ModuleCat.TorComparison.localizedModuleExtendScalarsIso P.primeCompl M).symm

set_option backward.isDefEq.respectTransparency false in
/-- Scalar extension is the literal tensor with the target ring for the
algebra structure defined by the specified ring map. -/
def extendScalarsLiteralTensorIso (f : R →+* S) (M : ModuleCat R) :
    letI : Algebra R S := f.toAlgebra
    (ModuleCat.extendScalars f).obj M ≅ ModuleCat.of S (S ⊗[R] M) := by
  letI : Algebra R S := f.toAlgebra
  exact Iso.refl _

/-- Localization of extension is the actual tensor over the source local ring,
with scalar action given by the literal localized map. -/
def primeLocalizedExtendTensorIso (f : R →+* S) (P : Ideal R) [P.IsPrime]
    (Q : Ideal S) [Q.IsPrime] (hPQ : P = Q.comap f) (M : ModuleCat R) :
    letI : Algebra (Localization.AtPrime P) (Localization.AtPrime Q) :=
      (Localization.localRingHom P Q f hPQ).toAlgebra
    ModuleCat.of (Localization.AtPrime Q)
        (LocalizedModule Q.primeCompl ((ModuleCat.extendScalars f).obj M)) ≅
      ModuleCat.of (Localization.AtPrime Q)
        (Localization.AtPrime Q ⊗[Localization.AtPrime P] LocalizedModule P.primeCompl M) :=
  primeLocalizedExtendScalarsIso f P Q hPQ M ≪≫
    extendScalarsLiteralTensorIso (Localization.localRingHom P Q f hPQ) _

/-- An actual module isomorphism induces an isomorphism of its literal prime
localizations, with the full local-ring action. -/
def primeLocalizedModuleMapIso (P : Ideal R) [P.IsPrime]
    {M N : ModuleCat R} (e : M ≅ N) :
    ModuleCat.of (Localization.AtPrime P) (LocalizedModule P.primeCompl M) ≅
      ModuleCat.of (Localization.AtPrime P) (LocalizedModule P.primeCompl N) :=
  _root_.ModuleCat.TorComparison.localizedModuleExtendScalarsIso P.primeCompl M ≪≫
    (ModuleCat.extendScalars (algebraMap R (Localization.AtPrime P))).mapIso e ≪≫
    (_root_.ModuleCat.TorComparison.localizedModuleExtendScalarsIso P.primeCompl N).symm

variable {k P T E W : Type u} [CommRing k] [CommRing P] [CommRing T]
  [CommRing E] [CommRing W] [Algebra k P] [Algebra k T] [Algebra k E] [Algebra k W]

/-- Surjectivity of the additional-factor map gives actual exterior surjectivity. -/
theorem exteriorAmbientMap_surjective (q : W →ₐ[k] E) (hq : Function.Surjective q) :
    Function.Surjective (exteriorAmbientMap (P := P) q) := by
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul p e =>
    obtain ⟨w, rfl⟩ := hq e
    exact ⟨p ⊗ₜ[k] w, rfl⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩

/-- The localized exterior quotient remains literally surjective. -/
theorem exteriorLocalAmbientMap_surjective (q : W →ₐ[k] E)
    (hq : Function.Surjective q) (Q : Ideal (P ⊗[k] E)) [Q.IsPrime] :
    Function.Surjective
      (Localization.localRingHom (Q.comap (exteriorAmbientMap q).toRingHom) Q
        (exteriorAmbientMap q).toRingHom rfl) :=
  _root_.ModuleCat.TorComparison.localRingHom_surjective (exteriorAmbientMap q).toRingHom
    (exteriorAmbientMap_surjective q hq) _ Q rfl

/-- Flatness of the actual local extension follows from flatness over the base;
the local quotient map is not asserted flat. -/
theorem exteriorLocalIncludeLeft_flat [Module.Flat k E]
    (Q : Ideal (P ⊗[k] E)) [Q.IsPrime] :
    (Localization.localRingHom
      (Q.comap (Algebra.TensorProduct.includeLeft : P →ₐ[k] P ⊗[k] E).toRingHom) Q
      (Algebra.TensorProduct.includeLeft : P →ₐ[k] P ⊗[k] E).toRingHom rfl).Flat :=
  exteriorIncludeLeft_flat.localRingHom Q _ rfl

/-- All-degree exterior Koszul homology localizes to the actual tensor of the
localized pair homology, restricted along the literal localized quotient.
All primes are the displayed contractions of Q; no genericity is assumed. -/
def exteriorPrimeLocalizedHomologyIso [Module.Flat k E]
    (σ : P →ₐ[k] T) (q : W →ₐ[k] E) (hq : Function.Surjective q)
    (Q : Ideal (P ⊗[k] E)) [Q.IsPrime] (t : List P) (n : ℕ) :
    let ρ := (exteriorAmbientMap (P := P) q).toRingHom
    let ι :=  (Algebra.TensorProduct.includeLeft : P →ₐ[k] P ⊗[k] E).toRingHom
    let p₆ := Q.comap ρ
    let p₀ := Q.comap ι
    letI : Algebra (Localization.AtPrime p₀) (Localization.AtPrime Q) :=
      (Localization.localRingHom p₀ Q ι rfl).toAlgebra
    ModuleCat.of (Localization.AtPrime p₆)
      (LocalizedModule p₆.primeCompl
        ((coefficientComplex
          ((ModuleCat.restrictScalars (Algebra.TensorProduct.map σ q).toRingHom).obj
            (ModuleCat.of (T ⊗[k] E) (T ⊗[k] E)))
          (t.map (Algebra.TensorProduct.includeLeft : P →ₐ[k] P ⊗[k] W))).homology n)) ≅
    (ModuleCat.restrictScalars (Localization.localRingHom p₆ Q ρ rfl)).obj
      (ModuleCat.of (Localization.AtPrime Q)
        (Localization.AtPrime Q ⊗[Localization.AtPrime p₀]
          LocalizedModule p₀.primeCompl
            ((coefficientComplex
              ((ModuleCat.restrictScalars σ.toRingHom).obj (ModuleCat.of T T)) t).homology n))) :=
  primeLocalizedModuleMapIso _ (exteriorCoefficientHomologyIso σ q t n) ≪≫
    _root_.ModuleCat.TorComparison.surjectivePrimeLocalizedModuleIso (exteriorAmbientMap
        q).toRingHom
      (exteriorAmbientMap_surjective q hq) _ Q rfl _ ≪≫
    (ModuleCat.restrictScalars
      (Localization.localRingHom (Q.comap (exteriorAmbientMap q).toRingHom) Q
        (exteriorAmbientMap q).toRingHom rfl)).mapIso
      (primeLocalizedExtendTensorIso
        (Algebra.TensorProduct.includeLeft : P →ₐ[k] P ⊗[k] E).toRingHom _ Q rfl _)

end ChainComplex.Koszul
