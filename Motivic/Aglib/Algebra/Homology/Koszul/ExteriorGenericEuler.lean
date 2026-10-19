/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.Koszul.ExteriorGenericMultiplicity
public import Motivic.Aglib.Algebra.Homology.Koszul.TwoListReplacement

/-!
# Bounded alternating generic exterior coefficients

The actual all-degree length comparison is summed over the literal bound
Fin(t.length + 1). Every integer length receives its proved finiteness input.
The resulting pair coefficient is identified with the accepted fixed-support
twoListGenericEuler at the actual contracted prime. The genuine closed-fiber
multiplicity remains a factor; no geometric prime or list attachment is assumed.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory _root_.HomologicalComplex.ModuleLengthEuler
open scoped TensorProduct

namespace ChainComplex.Koszul

variable {k P T E W : Type u} [CommRing k] [CommRing P] [CommRing T]
  [CommRing E] [CommRing W] [Algebra k P] [Algebra k T] [Algebra k E] [Algebra k W]
  [Module.Flat k E]

/-- The actual pair-support generic prime is the literal contraction along the
flat exterior inclusion. Its minimality is proved from the extended support. -/
def coordinatePairGenericPrime (σ : P →ₐ[k] T)
    (Q : Ideal (P ⊗[k] E)) [Q.IsPrime] (t : List P)
    (hQ : Q ∈ ((coordinateKoszulSupport σ.toRingHom t).map
      (Algebra.TensorProduct.includeLeft : P →ₐ[k] P ⊗[k] E).toRingHom).minimalPrimes) :
    (Ideal.ofList t ⊔ Module.annihilator P (coordinateCoefficient σ.toRingHom)).minimalPrimes := by
  refine ⟨Q.under P, ?_⟩
  rw [coordinateCoefficient_annihilator]
  exact Module.flatGeneric_under_mem_minimalPrimes
    (coordinateKoszulSupport σ.toRingHom t) Q hQ

variable [IsNoetherianRing P] [IsNoetherianRing (P ⊗[k] E)]

/-- The actual localized pair length, converted only after its finiteness proof. -/
def pairGenericIntegerLength (σ : P →ₐ[k] T) (hσ : Function.Surjective σ)
    (Q : Ideal (P ⊗[k] E)) [Q.IsPrime] (t : List P)
    (hQ : Q ∈ ((coordinateKoszulSupport σ.toRingHom t).map
      (Algebra.TensorProduct.includeLeft : P →ₐ[k] P ⊗[k] E).toRingHom).minimalPrimes)
    (n : ℕ) : ℤ := by
  let := coordinateKoszulHomology_finite σ.toRingHom hσ t n
  exact integerLength (R := Localization.AtPrime (Q.under P)) (pairLocalizedHomology σ Q t n)
    (localGeneric_factors_ne_top (coordinateKoszulHomology σ.toRingHom t n)
      (coordinateKoszulSupport σ.toRingHom t)
      (coordinateKoszulSupport_annihilates σ.toRingHom t n) Q hQ).1

/-- The genuine integer closed-fiber multiplicity, with its finite length proved
at the selected generic point of the extended support. -/
def genericClosedFiberMultiplicity (σ : P →ₐ[k] T) (hσ : Function.Surjective σ)
    (Q : Ideal (P ⊗[k] E)) [Q.IsPrime] (t : List P)
    (hQ : Q ∈ ((coordinateKoszulSupport σ.toRingHom t).map
      (Algebra.TensorProduct.includeLeft : P →ₐ[k] P ⊗[k] E).toRingHom).minimalPrimes) : ℤ := by
  let := coordinateKoszulHomology_finite σ.toRingHom hσ t 0
  have h := localGeneric_factors_ne_top (coordinateKoszulHomology σ.toRingHom t 0)
    (coordinateKoszulSupport σ.toRingHom t)
    (coordinateKoszulSupport_annihilates σ.toRingHom t 0) Q hQ
  exact integerLength _ h.2

/-- The actual exterior localized length, converted only after its finiteness proof. -/
def exteriorGenericIntegerLength (σ : P →ₐ[k] T) (hσ : Function.Surjective σ)
    (q : W →ₐ[k] E) (hq : Function.Surjective q)
    (Q : Ideal (P ⊗[k] E)) [Q.IsPrime] (t : List P)
    (hQ : Q ∈ ((coordinateKoszulSupport σ.toRingHom t).map
      (Algebra.TensorProduct.includeLeft : P →ₐ[k] P ⊗[k] E).toRingHom).minimalPrimes)
    (n : ℕ) : ℤ :=
  integerLength (R := Localization.AtPrime (Q.comap (exteriorAmbientMap q).toRingHom))
    (exteriorLocalizedHomology σ q Q t n)
    (exteriorGeneric_lengths_ne_top σ hσ q hq Q t hQ n).1

/-- Integer conversion preserves the proved actual degreewise length product. -/
theorem exteriorGeneric_integerLength_eq_mul (σ : P →ₐ[k] T) (hσ : Function.Surjective σ)
    (q : W →ₐ[k] E) (hq : Function.Surjective q)
    (Q : Ideal (P ⊗[k] E)) [Q.IsPrime] (t : List P)
    (hQ : Q ∈ ((coordinateKoszulSupport σ.toRingHom t).map
      (Algebra.TensorProduct.includeLeft : P →ₐ[k] P ⊗[k] E).toRingHom).minimalPrimes)
    (n : ℕ) :
    exteriorGenericIntegerLength σ hσ q hq Q t hQ n =
      pairGenericIntegerLength σ hσ Q t hQ n * genericClosedFiberMultiplicity σ hσ Q t hQ := by
  simp only [exteriorGenericIntegerLength, pairGenericIntegerLength,
    genericClosedFiberMultiplicity, integerLength, exteriorGeneric_homology_length σ hσ q hq Q t hQ,
    ENat.toNat_mul, Nat.cast_mul]
  rfl

/-- The bounded alternating coefficient of the actual localized pair homology. -/
def pairGenericEuler (σ : P →ₐ[k] T) (hσ : Function.Surjective σ)
    (Q : Ideal (P ⊗[k] E)) [Q.IsPrime] (t : List P)
    (hQ : Q ∈ ((coordinateKoszulSupport σ.toRingHom t).map
      (Algebra.TensorProduct.includeLeft : P →ₐ[k] P ⊗[k] E).toRingHom).minimalPrimes) : ℤ :=
  ∑ n : Fin (t.length + 1), (-1 : ℤ) ^ (n : ℕ) * pairGenericIntegerLength σ hσ Q t hQ n

/-- The bounded alternating coefficient of the actual exterior homology at the
literal ambient-prime contraction, retaining every degree through t.length. -/
def exteriorGenericEuler (σ : P →ₐ[k] T) (hσ : Function.Surjective σ)
    (q : W →ₐ[k] E) (hq : Function.Surjective q)
    (Q : Ideal (P ⊗[k] E)) [Q.IsPrime] (t : List P)
    (hQ : Q ∈ ((coordinateKoszulSupport σ.toRingHom t).map
      (Algebra.TensorProduct.includeLeft : P →ₐ[k] P ⊗[k] E).toRingHom).minimalPrimes) : ℤ :=
  ∑ n : Fin (t.length + 1), (-1 : ℤ) ^ (n : ℕ) *
    exteriorGenericIntegerLength σ hσ q hq Q t hQ n

/-- The actual alternating generic exterior coefficient factors by the genuine
closed-fiber multiplicity, over the literal common finite degree bound. -/
theorem exteriorGenericEuler_eq_pair_mul (σ : P →ₐ[k] T) (hσ : Function.Surjective σ)
    (q : W →ₐ[k] E) (hq : Function.Surjective q)
    (Q : Ideal (P ⊗[k] E)) [Q.IsPrime] (t : List P)
    (hQ : Q ∈ ((coordinateKoszulSupport σ.toRingHom t).map
      (Algebra.TensorProduct.includeLeft : P →ₐ[k] P ⊗[k] E).toRingHom).minimalPrimes) :
    exteriorGenericEuler σ hσ q hq Q t hQ =
      pairGenericEuler σ hσ Q t hQ * genericClosedFiberMultiplicity σ hσ Q t hQ := by
  simp only [exteriorGenericEuler, pairGenericEuler, exteriorGeneric_integerLength_eq_mul,
    ← mul_assoc, Finset.sum_mul]

/-- The pair-side bounded coefficient is exactly the accepted two-list generic
replacement coefficient at the constructed contracted prime, with its actual
LocalizedModule-to-tensor comparison and proved kernel annihilator. -/
theorem pairGenericEuler_eq_twoListGenericEuler (σ : P →ₐ[k] T) (hσ : Function.Surjective σ)
    (Q : Ideal (P ⊗[k] E)) [Q.IsPrime] (t : List P)
    (hQ : Q ∈ ((coordinateKoszulSupport σ.toRingHom t).map
      (Algebra.TensorProduct.includeLeft : P →ₐ[k] P ⊗[k] E).toRingHom).minimalPrimes) :
    letI := coordinateCoefficient_finite σ.toRingHom hσ
    pairGenericEuler σ hσ Q t hQ =
      twoListGenericEuler (coordinateCoefficient σ.toRingHom) t
        (coordinatePairGenericPrime σ Q t hQ) := by
  let := coordinateCoefficient_finite σ.toRingHom hσ
  unfold pairGenericEuler twoListGenericEuler
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  simp only [pairGenericIntegerLength, fixedSupportGenericLength, integerLength,
    coordinatePairGenericPrime, pairLocalizedHomology]
  rw [(LocalizedModule.equivTensorProduct (Q.under P).primeCompl
    (coordinateKoszulHomology σ.toRingHom t n)).length_eq]
  rfl

/-- The literal exterior alternating coefficient equals the existing pair
replacement coefficient times the retained actual closed-fiber multiplicity. -/
theorem exteriorGenericEuler_eq_twoListGenericEuler_mul
    (σ : P →ₐ[k] T) (hσ : Function.Surjective σ)
    (q : W →ₐ[k] E) (hq : Function.Surjective q)
    (Q : Ideal (P ⊗[k] E)) [Q.IsPrime] (t : List P)
    (hQ : Q ∈ ((coordinateKoszulSupport σ.toRingHom t).map
      (Algebra.TensorProduct.includeLeft : P →ₐ[k] P ⊗[k] E).toRingHom).minimalPrimes) :
    letI := coordinateCoefficient_finite σ.toRingHom hσ
    exteriorGenericEuler σ hσ q hq Q t hQ =
      twoListGenericEuler (coordinateCoefficient σ.toRingHom) t
          (coordinatePairGenericPrime σ Q t hQ) * genericClosedFiberMultiplicity σ hσ Q t hQ := by
  let := coordinateCoefficient_finite σ.toRingHom hσ
  rw [exteriorGenericEuler_eq_pair_mul, pairGenericEuler_eq_twoListGenericEuler]

end ChainComplex.Koszul
