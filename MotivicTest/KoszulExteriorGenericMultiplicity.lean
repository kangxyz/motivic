/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulExteriorGenericMultiplicity
public import Motivic.AlgebraicGeometry.Diagonal.AffineMiddleSupports
public import MotivicTest.FlatGenericDualNumbers

/-!
# Actual exterior generic multiplicity consumers

These consumers use the three arbitrary support quotients, including
nonradical ideals, and preserve every degree of the actual Koszul homology.
A computed dual-number fiber retains its genuine multiplicity two.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Motivic.Koszul
open scoped TensorProduct Motivic.MiddleDiagonal

namespace MotivicTest.KoszulExteriorGenericMultiplicity

section ActualSupports

variable (k A B C D : Type u) [Field k] [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra k A] [Algebra k B] [Algebra k C] [Algebra k D]
  (I : Ideal (A ⊗[k] B)) (J : Ideal (B ⊗[k] C)) (K : Ideal (C ⊗[k] D))

local notation "P₀" => Motivic.MiddleDiagonal.ambientRing k A B C
local notation "T₀" => ((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J)
local notation "E₀" => (C ⊗[k] D) ⧸ K
local notation "S₀" => P₀ ⊗[k] E₀
local notation "σ₀" => Motivic.AffineMiddle.supportRingMap k A B C I J
local notation "q₀" => Ideal.Quotient.mkₐ k K
local notation "λ₀" => (Algebra.TensorProduct.includeLeft : P₀ →ₐ[k] S₀)
local notation "ρ₀" => (exteriorAmbientMap (P := P₀) q₀)

/-- Cache the canonical pair-support ring before adding the third factor. -/
local instance pairSupportCommRing : CommRing T₀ := inferInstance

/-- Cache the same canonical pair-support algebra structure. -/
local instance pairSupportAlgebra : Algebra k T₀ := inferInstance

/-- Cache the canonical exterior scalar ring before prime localization. -/
local instance exteriorScalarCommRing : CommRing S₀ := inferInstance

/-- The support ideal is derived from the actual nonreduced quotient action. -/
theorem actualPairAnnihilation (t : List P₀) (n : ℕ) :
    Ideal.ofList t ⊔ RingHom.ker (σ₀).toRingHom ≤
      Module.annihilator P₀ (coordinateKoszulHomology (σ₀).toRingHom t n) :=
  coordinateKoszulSupport_annihilates (σ₀).toRingHom t n

variable [IsNoetherianRing (Motivic.MiddleDiagonal.ambientRing k A B C)]

/-- Genuine finite generation follows from the actual support quotient surjection. -/
theorem actualPairFinite (t : List P₀) (n : ℕ) :
    Module.Finite P₀ (coordinateKoszulHomology (σ₀).toRingHom t n) :=
  coordinateKoszulHomology_finite (σ₀).toRingHom
    (Motivic.AffineMiddle.supportRingMap_surjective k A B C I J) t n

variable (Q : Ideal (Motivic.MiddleDiagonal.ambientRing k A B C ⊗[k]
  ((C ⊗[k] D) ⧸ K))) [Q.IsPrime]

/-- Every actual exterior homology degree has the full generic fiber multiplier. -/
theorem actualExteriorGenericLength (t : List P₀)
    (hQ : Q ∈ ((Ideal.ofList t ⊔ RingHom.ker (σ₀).toRingHom).map (λ₀).toRingHom).minimalPrimes)
    (n : ℕ) :
    Module.length (Localization.AtPrime (Q.comap (ρ₀).toRingHom))
        (exteriorLocalizedHomology σ₀ q₀ Q t n) =
      Module.length (Localization.AtPrime (Q.under P₀)) (pairLocalizedHomology σ₀ Q t n) *
        Module.length (Localization.AtPrime (R := S₀) Q)
          (primeLocalClosedFiber (R := P₀) (S := S₀) (λ₀).toRingHom Q) :=
  exteriorGeneric_homology_length σ₀
    (Motivic.AffineMiddle.supportRingMap_surjective k A B C I J)
    q₀ Ideal.Quotient.mk_surjective Q t hQ n

/-- Repeated and zero equations are not replaced by a degree-zero coefficient. -/
theorem actualRepeatedZeroGenericLength (a : P₀)
    (hQ : Q ∈ ((Ideal.ofList [a, a, 0] ⊔ RingHom.ker (σ₀).toRingHom).map
      (λ₀).toRingHom).minimalPrimes) (n : ℕ) :
    Module.length (Localization.AtPrime (Q.comap (ρ₀).toRingHom))
        (exteriorLocalizedHomology σ₀ q₀ Q [a, a, 0] n) =
      Module.length (Localization.AtPrime (Q.under P₀))
          (pairLocalizedHomology σ₀ Q [a, a, 0] n) *
        Module.length (Localization.AtPrime (R := S₀) Q)
          (primeLocalClosedFiber (R := P₀) (S := S₀) (λ₀).toRingHom Q) :=
  actualExteriorGenericLength k A B C D I J K Q [a, a, 0] hQ n

/-- All lengths are proved finite under the actual two ambient Noetherian hypotheses. -/
theorem actualGenericLengthsFinite [IsNoetherianRing S₀] (t : List P₀)
    (hQ : Q ∈ ((Ideal.ofList t ⊔ RingHom.ker (σ₀).toRingHom).map (λ₀).toRingHom).minimalPrimes)
    (n : ℕ) :
    Module.length (Localization.AtPrime (Q.comap (ρ₀).toRingHom))
        (exteriorLocalizedHomology σ₀ q₀ Q t n) ≠ ⊤ ∧
      Module.length (Localization.AtPrime (Q.under P₀)) (pairLocalizedHomology σ₀ Q t n) ≠ ⊤ ∧
      Module.length (Localization.AtPrime (R := S₀) Q)
          (primeLocalClosedFiber (R := P₀) (S := S₀) (λ₀).toRingHom Q) ≠ ⊤ :=
  exteriorGeneric_lengths_ne_top σ₀
    (Motivic.AffineMiddle.supportRingMap_surjective k A B C I J)
    q₀ Ideal.Quotient.mk_surjective Q t hQ n

end ActualSupports

section NonreducedFiber

open FlatGenericDualNumbers

variable (k : Type u) [Field k]

/-- The literal local maximal-ideal fiber retains its calculated nilpotent multiplicity. -/
theorem literalClosedFiber_length_two :
    Module.length (Localization.AtPrime (genericPrime k))
      (primeLocalClosedFiber (algebraMap k (dualNumbers k)) (genericPrime k)) = 2 := by
  dsimp only [primeLocalClosedFiber]
  rw [primeLocalClosedFiber_ideal (R := k) (genericPrime k)]
  exact closedFiber_length_two k

-- Nested square-zero and two local scalar structures require three pending instance levels.
set_option maxSynthPendingDepth 3 in
/-- The new source-local tensor comparison retains the computed nonreduced factor two. -/
theorem literalLocalTensor_factor_two :
    letI : Algebra (Localization.AtPrime ((genericPrime k).under k))
        (Localization.AtPrime (genericPrime k)) :=
      (Localization.localRingHom ((genericPrime k).under k) (genericPrime k)
        (algebraMap k (dualNumbers k)) rfl).toAlgebra
    Module.length (Localization.AtPrime (genericPrime k))
        (Localization.AtPrime (genericPrime k) ⊗[Localization.AtPrime ((genericPrime k).under k)]
          LocalizedModule ((genericPrime k).under k).primeCompl (k × k)) =
      Module.length (Localization.AtPrime ((genericPrime k).under k))
        (LocalizedModule ((genericPrime k).under k).primeCompl (k × k)) * 2 := by
  let : Algebra (Localization.AtPrime ((genericPrime k).under k))
      (Localization.AtPrime (genericPrime k)) :=
    (Localization.localRingHom ((genericPrime k).under k) (genericPrime k)
      (algebraMap k (dualNumbers k)) rfl).toAlgebra
  have h := localTensorGeneric_length (ModuleCat.of k (k × k)) ⊥ bot_le (genericPrime k)
    (by simpa only [Ideal.map_bot] using genericPrime_minimal k)
  rw [literalClosedFiber_length_two] at h
  exact h

end NonreducedFiber

end MotivicTest.KoszulExteriorGenericMultiplicity
