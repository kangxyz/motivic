/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.Koszul.ExteriorCoefficientLocalization
public import Motivic.Aglib.Algebra.Homology.Koszul.FiniteSupport.Basic
public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.AmbientLength
public import Motivic.Aglib.RingTheory.LocalLength.FlatGenericMultiplicity

/-!
# Actual generic lengths of exterior Koszul homology

The literal quotient action determines its kernel annihilator and finite
coefficient module. Every actual pair Koszul homology is finite and is killed
by the list ideal plus that kernel. At an algebraic generic point of the
extended support, the localized exterior homology length is the pair-local
length times the actual closed-fiber multiplicity. No fiber multiplicity is
removed, and no geometric point identification or Tor comparison is assumed.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory
open scoped TensorProduct

namespace ChainComplex.Koszul

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The coordinate coefficient module retains the literal ring-map action. -/
abbrev coordinateCoefficient (f : R →+* S) : ModuleCat R :=
  (ModuleCat.restrictScalars f).obj (ModuleCat.of S S)

/-- The coefficient annihilator equals the actual kernel, including nilpotents. -/
theorem coordinateCoefficient_annihilator (f : R →+* S) :
    Module.annihilator R (coordinateCoefficient f) = RingHom.ker f := by
  ext r
  rw [Module.mem_annihilator, RingHom.mem_ker]
  change (∀ m : S, f r * m = 0) ↔ f r = 0
  constructor
  · intro hr
    simpa using hr 1
  · intro hr m
    rw [hr, zero_mul]

set_option backward.isDefEq.respectTransparency false in
/-- A surjective coordinate map gives genuine finite generation over the ambient ring. -/
theorem coordinateCoefficient_finite (f : R →+* S) (hf : Function.Surjective f) :
    Module.Finite R (coordinateCoefficient f) := by
  let : Algebra R S := f.toAlgebra
  exact Module.Finite.of_surjective (Algebra.linearMap R S) hf

/-- The actual pairwise Koszul homology with its specified quotient-ring action. -/
abbrev coordinateKoszulHomology (f : R →+* S) (t : List R) (n : ℕ) : ModuleCat R :=
  (coefficientComplex (coordinateCoefficient f) t).homology n

/-- The fixed first-stage support ideal is the list ideal plus the literal kernel. -/
abbrev coordinateKoszulSupport (f : R →+* S) (t : List R) : Ideal R :=
  Ideal.ofList t ⊔ RingHom.ker f

/-- The actual first-stage support ideal annihilates every homology degree. -/
theorem coordinateKoszulSupport_annihilates (f : R →+* S) (t : List R) (n : ℕ) :
    coordinateKoszulSupport f t ≤ Module.annihilator R (coordinateKoszulHomology f t n) := by
  rw [coordinateKoszulSupport, ← coordinateCoefficient_annihilator f]
  exact support_le_annihilator_coefficient_homology (coordinateCoefficient f) t n

/-- Finite generation of pair homology is derived from Noetherianity and the
actual quotient map, without assuming finite length or regularity. -/
theorem coordinateKoszulHomology_finite [IsNoetherianRing R]
    (f : R →+* S) (hf : Function.Surjective f) (t : List R) (n : ℕ) :
    Module.Finite R (coordinateKoszulHomology f t n) := by
  let := coordinateCoefficient_finite f hf
  infer_instance

/-- Extension along the canonical algebra map is the canonical tensor module. -/
def extendScalarsCanonicalTensorIso [Algebra R S] (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalars (algebraMap R S)).obj M ≅ ModuleCat.of S (S ⊗[R] M) := by
  let A := (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)
  letI : IsScalarTower R S A := IsScalarTower.of_compHom R S _
  let e : A ≃ₗ[S] S := LinearEquiv.refl _ _
  exact (TensorProduct.AlgebraTensorModule.congr e (LinearEquiv.refl R M)).toModuleIso

/-- Literal localization of scalar extension is the canonical target-local tensor. -/
def localizedExtendCanonicalTensorIso [Algebra R S]
    (Q : Ideal S) [Q.IsPrime] (M : ModuleCat.{u} R) :
    ModuleCat.of (Localization.AtPrime Q)
      (LocalizedModule Q.primeCompl ((ModuleCat.extendScalars (algebraMap R S)).obj M)) ≅
    ModuleCat.of (Localization.AtPrime Q)
      (Localization.AtPrime Q ⊗[S] (S ⊗[R] M)) :=
  primeLocalizedModuleMapIso Q (extendScalarsCanonicalTensorIso M) ≪≫
    (LocalizedModule.equivTensorProduct Q.primeCompl (S ⊗[R] M)).toModuleIso

/-- The source-local tensor with literal localRingHom action matches exactly
the double tensor used by the proved generic multiplicity theorem. -/
def localTensorCanonicalBaseChangeIso [Algebra R S]
    (Q : Ideal S) [Q.IsPrime] (M : ModuleCat.{u} R) :
    letI : Algebra (Localization.AtPrime (Q.under R)) (Localization.AtPrime Q) :=
      (Localization.localRingHom (Q.under R) Q (algebraMap R S) rfl).toAlgebra
    ModuleCat.of (Localization.AtPrime Q)
      (Localization.AtPrime Q ⊗[Localization.AtPrime (Q.under R)]
        LocalizedModule (Q.under R).primeCompl M) ≅
    ModuleCat.of (Localization.AtPrime Q)
      (Localization.AtPrime Q ⊗[S] (S ⊗[R] M)) :=
  (primeLocalizedExtendTensorIso (algebraMap R S) (Q.under R) Q rfl M).symm ≪≫
    localizedExtendCanonicalTensorIso Q M

/-- The actual closed fiber is cut out by the maximal ideal of the source local ring. -/
abbrev primeLocalClosedFiber (f : R →+* S) (Q : Ideal S) [Q.IsPrime] :=
  Localization.AtPrime Q ⧸
    (IsLocalRing.maximalIdeal (Localization.AtPrime (Q.comap f))).map
      (Localization.localRingHom (Q.comap f) Q f rfl)

/-- The local maximal-ideal extension is the literal contraction-ideal extension. -/
theorem primeLocalClosedFiber_ideal [Algebra R S] (Q : Ideal S) [Q.IsPrime] :
    (IsLocalRing.maximalIdeal (Localization.AtPrime (Q.under R))).map
        (Localization.localRingHom (Q.under R) Q (algebraMap R S) rfl) =
      (Q.under R).map (algebraMap R (Localization.AtPrime Q)) := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, primeLocalRingHom_square]
  rw [IsScalarTower.algebraMap_eq R S (Localization.AtPrime Q)]

/-- Generic length of the literal source-local tensor, with the true local
closed-fiber multiplicity and actual LocalizedModule source length. -/
theorem localTensorGeneric_length [Algebra R S] [IsNoetherianRing R] [Module.Flat R S]
    (M : ModuleCat.{u} R) [Module.Finite R M] (I : Ideal R)
    (hI : I ≤ Module.annihilator R M) (Q : Ideal S) [Q.IsPrime]
    (hQ : Q ∈ (I.map (algebraMap R S)).minimalPrimes) :
    letI : Algebra (Localization.AtPrime (Q.under R)) (Localization.AtPrime Q) :=
      (Localization.localRingHom (Q.under R) Q (algebraMap R S) rfl).toAlgebra
    Module.length (Localization.AtPrime Q)
        (Localization.AtPrime Q ⊗[Localization.AtPrime (Q.under R)]
          LocalizedModule (Q.under R).primeCompl M) =
      Module.length (Localization.AtPrime (Q.under R))
          (LocalizedModule (Q.under R).primeCompl M) *
        Module.length (Localization.AtPrime Q) (primeLocalClosedFiber (algebraMap R S) Q) := by
  let : Algebra (Localization.AtPrime (Q.under R)) (Localization.AtPrime Q) :=
    (Localization.localRingHom (Q.under R) Q (algebraMap R S) rfl).toAlgebra
  refine (localTensorCanonicalBaseChangeIso Q M).toLinearEquiv.length_eq.trans ?_
  have h := Module.flatGeneric_multiplicity M I hI Q hQ
  rw [← (LocalizedModule.equivTensorProduct (Q.under R).primeCompl M).length_eq] at h
  dsimp only [primeLocalClosedFiber]
  rw [primeLocalClosedFiber_ideal (R := R) Q]
  exact h

/-- Pair-local length and the genuine closed-fiber length are finite at a
minimal prime of the extended fixed support, before any integer conversion. -/
theorem localGeneric_factors_ne_top [Algebra R S] [IsNoetherianRing R]
    [IsNoetherianRing S] [Module.Flat R S]
    (M : ModuleCat.{u} R) [Module.Finite R M] (I : Ideal R)
    (hI : I ≤ Module.annihilator R M) (Q : Ideal S) [Q.IsPrime]
    (hQ : Q ∈ (I.map (algebraMap R S)).minimalPrimes) :
    Module.length (Localization.AtPrime (Q.under R))
        (LocalizedModule (Q.under R).primeCompl M) ≠ ⊤ ∧
      Module.length (Localization.AtPrime Q)
        (primeLocalClosedFiber (algebraMap R S) Q) ≠ ⊤ := by
  have h := Module.flatGeneric_lengths_ne_top M I hI Q hQ
  constructor
  · rw [(LocalizedModule.equivTensorProduct (Q.under R).primeCompl M).length_eq]
    exact h.1
  · dsimp only [primeLocalClosedFiber]
    rw [primeLocalClosedFiber_ideal (R := R) Q]
    exact h.2.2

variable {k P T E W : Type u} [CommRing k] [CommRing P] [CommRing T]
  [CommRing E] [CommRing W] [Algebra k P] [Algebra k T] [Algebra k E] [Algebra k W]

/-- The actual exterior homology localized at the literal ambient-prime contraction. -/
abbrev exteriorLocalizedHomology (σ : P →ₐ[k] T) (q : W →ₐ[k] E)
    (Q : Ideal (P ⊗[k] E)) [Q.IsPrime] (t : List P) (n : ℕ) :
    ModuleCat (Localization.AtPrime (Q.comap (exteriorAmbientMap q).toRingHom)) :=
  ModuleCat.of (Localization.AtPrime (Q.comap (exteriorAmbientMap q).toRingHom))
    (LocalizedModule (Q.comap (exteriorAmbientMap q).toRingHom).primeCompl
      (coordinateKoszulHomology (Algebra.TensorProduct.map σ q).toRingHom
        (t.map (Algebra.TensorProduct.includeLeft : P →ₐ[k] P ⊗[k] W)) n))

/-- The actual pair homology localized at the contraction along the flat exterior inclusion. -/
abbrev pairLocalizedHomology (σ : P →ₐ[k] T)
    (Q : Ideal (P ⊗[k] E)) [Q.IsPrime] (t : List P) (n : ℕ) :
    ModuleCat (Localization.AtPrime (Q.under P)) :=
  ModuleCat.of (Localization.AtPrime (Q.under P))
    (LocalizedModule (Q.under P).primeCompl (coordinateKoszulHomology σ.toRingHom t n))

/-- The actual generic exterior homology coefficient equals its pair-local
coefficient times the literal closed-fiber length. All annihilation and module
finiteness are derived from the actual quotient map and ambient Noetherianity. -/
theorem exteriorGeneric_homology_length [IsNoetherianRing P] [Module.Flat k E]
    (σ : P →ₐ[k] T) (hσ : Function.Surjective σ) (q : W →ₐ[k] E)
    (hq : Function.Surjective q) (Q : Ideal (P ⊗[k] E)) [Q.IsPrime]
    (t : List P)
    (hQ : Q ∈ ((coordinateKoszulSupport σ.toRingHom t).map
      (Algebra.TensorProduct.includeLeft : P →ₐ[k] P ⊗[k] E).toRingHom).minimalPrimes)
    (n : ℕ) :
    Module.length (Localization.AtPrime (Q.comap (exteriorAmbientMap q).toRingHom))
        (exteriorLocalizedHomology σ q Q t n) =
      Module.length (Localization.AtPrime (Q.under P)) (pairLocalizedHomology σ Q t n) *
        Module.length (Localization.AtPrime Q)
          (primeLocalClosedFiber
            (Algebra.TensorProduct.includeLeft : P →ₐ[k] P ⊗[k] E).toRingHom Q) := by
  let := coordinateKoszulHomology_finite σ.toRingHom hσ t n
  refine (exteriorPrimeLocalizedHomologyIso σ q hq Q t n).toLinearEquiv.length_eq.trans ?_
  refine (_root_.ModuleCat.length_restrictScalars_of_surjective
    (Localization.localRingHom (Q.comap (exteriorAmbientMap q).toRingHom) Q
      (exteriorAmbientMap q).toRingHom rfl)
    (exteriorLocalAmbientMap_surjective q hq Q) _).trans ?_
  exact localTensorGeneric_length (coordinateKoszulHomology σ.toRingHom t n)
    (coordinateKoszulSupport σ.toRingHom t)
    (coordinateKoszulSupport_annihilates σ.toRingHom t n) Q hQ

/-- All three actual lengths in the exterior multiplicity identity are finite
under the two ambient Noetherian hypotheses. The fiber factor is preserved. -/
theorem exteriorGeneric_lengths_ne_top [IsNoetherianRing P]
    [IsNoetherianRing (P ⊗[k] E)] [Module.Flat k E]
    (σ : P →ₐ[k] T) (hσ : Function.Surjective σ) (q : W →ₐ[k] E)
    (hq : Function.Surjective q) (Q : Ideal (P ⊗[k] E)) [Q.IsPrime]
    (t : List P)
    (hQ : Q ∈ ((coordinateKoszulSupport σ.toRingHom t).map
      (Algebra.TensorProduct.includeLeft : P →ₐ[k] P ⊗[k] E).toRingHom).minimalPrimes)
    (n : ℕ) :
    Module.length (Localization.AtPrime (Q.comap (exteriorAmbientMap q).toRingHom))
        (exteriorLocalizedHomology σ q Q t n) ≠ ⊤ ∧
      Module.length (Localization.AtPrime (Q.under P)) (pairLocalizedHomology σ Q t n) ≠ ⊤ ∧
      Module.length (Localization.AtPrime Q)
        (primeLocalClosedFiber
          (Algebra.TensorProduct.includeLeft : P →ₐ[k] P ⊗[k] E).toRingHom Q) ≠ ⊤ := by
  let := coordinateKoszulHomology_finite σ.toRingHom hσ t n
  have h := localGeneric_factors_ne_top (coordinateKoszulHomology σ.toRingHom t n)
    (coordinateKoszulSupport σ.toRingHom t)
    (coordinateKoszulSupport_annihilates σ.toRingHom t n) Q hQ
  refine ⟨?_, h.1, h.2⟩
  rw [exteriorGeneric_homology_length σ hσ q hq Q t hQ n]
  exact WithTop.mul_ne_top h.1 h.2

end ChainComplex.Koszul
