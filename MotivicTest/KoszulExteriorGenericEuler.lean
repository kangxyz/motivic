/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulExteriorGenericEuler
public import Motivic.AlgebraicGeometry.Diagonal.AffineMiddleSupports

/-!
# Actual support consumers of alternating exterior coefficients

The bounded coefficient factorization is applied to the three arbitrary
support quotient ideals. The pair term is the existing two-list replacement
coefficient at the proved contracted prime, rather than an assumed scalar.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Motivic.Koszul
open scoped TensorProduct Motivic.MiddleDiagonal

namespace MotivicTest.KoszulExteriorGenericEuler

variable (k A B C D : Type u) [Field k] [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra k A] [Algebra k B] [Algebra k C] [Algebra k D]
  (I : Ideal (A ⊗[k] B)) (J : Ideal (B ⊗[k] C)) (K : Ideal (C ⊗[k] D))

local notation "P₀" => Motivic.MiddleDiagonal.ambientRing k A B C
local notation "T₀" => ((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J)
local notation "E₀" => (C ⊗[k] D) ⧸ K
local notation "S₀" => P₀ ⊗[k] E₀
local notation "σ₀" => Motivic.AffineMiddle.supportRingMap k A B C I J
local notation "hσ₀" => Motivic.AffineMiddle.supportRingMap_surjective k A B C I J
local notation "q₀" => Ideal.Quotient.mkₐ k K
local notation "λ₀" => (Algebra.TensorProduct.includeLeft : P₀ →ₐ[k] S₀)

/-- Cache the canonical pair-support ring before adding the exterior factor. -/
local instance pairSupportCommRing : CommRing T₀ := inferInstance

/-- Cache the canonical pair-support field-algebra structure. -/
local instance pairSupportAlgebra : Algebra k T₀ := inferInstance

/-- Cache the same canonical exterior scalar ring used by prime localization. -/
local instance exteriorScalarCommRing : CommRing S₀ := inferInstance

variable (Q : Ideal (Motivic.MiddleDiagonal.ambientRing k A B C ⊗[k]
  ((C ⊗[k] D) ⧸ K))) [Q.IsPrime]

/-- The actual pair generic point is the literal prime contraction. -/
theorem actualPairGenericPrime (t : List P₀)
    (hQ : Q ∈ ((Ideal.ofList t ⊔ RingHom.ker (σ₀).toRingHom).map
      (λ₀).toRingHom).minimalPrimes) :
    (coordinatePairGenericPrime σ₀ Q t hQ).1 = Q.under P₀ := rfl

variable [IsNoetherianRing (Motivic.MiddleDiagonal.ambientRing k A B C)]
  [IsNoetherianRing (Motivic.MiddleDiagonal.ambientRing k A B C ⊗[k] ((C ⊗[k] D) ⧸ K))]

/-- The actual alternating exterior coefficient is the existing pair replacement
coefficient multiplied by the retained genuine fiber multiplicity. -/
theorem actualExteriorGenericEuler (t : List P₀)
    (hQ : Q ∈ ((Ideal.ofList t ⊔ RingHom.ker (σ₀).toRingHom).map
      (λ₀).toRingHom).minimalPrimes) :
    letI := coordinateCoefficient_finite (σ₀).toRingHom hσ₀
    exteriorGenericEuler σ₀ hσ₀ q₀ Ideal.Quotient.mk_surjective Q t hQ =
      twoListGenericEuler (coordinateCoefficient (σ₀).toRingHom) t
          (coordinatePairGenericPrime σ₀ Q t hQ) * genericClosedFiberMultiplicity σ₀ hσ₀ Q t hQ :=
  exteriorGenericEuler_eq_twoListGenericEuler_mul σ₀ hσ₀ q₀
    Ideal.Quotient.mk_surjective Q t hQ

/-- Repeated and zero equations keep the full literal alternating degree bound. -/
theorem actualRepeatedZeroEuler (a : P₀)
    (hQ : Q ∈ ((Ideal.ofList [a, a, 0] ⊔ RingHom.ker (σ₀).toRingHom).map
      (λ₀).toRingHom).minimalPrimes) :
    letI := coordinateCoefficient_finite (σ₀).toRingHom hσ₀
    exteriorGenericEuler σ₀ hσ₀ q₀ Ideal.Quotient.mk_surjective Q [a, a, 0] hQ =
      twoListGenericEuler (coordinateCoefficient (σ₀).toRingHom) [a, a, 0]
          (coordinatePairGenericPrime σ₀ Q [a, a, 0] hQ) *
        genericClosedFiberMultiplicity σ₀ hσ₀ Q [a, a, 0] hQ :=
  actualExteriorGenericEuler k A B C D I J K Q [a, a, 0] hQ

/-- The empty list retains its one degree-zero contribution. -/
theorem actualEmptyEuler
    (hQ : Q ∈ ((Ideal.ofList ([] : List P₀) ⊔ RingHom.ker (σ₀).toRingHom).map
      (λ₀).toRingHom).minimalPrimes) :
    exteriorGenericEuler σ₀ hσ₀ q₀ Ideal.Quotient.mk_surjective Q [] hQ =
      exteriorGenericIntegerLength σ₀ hσ₀ q₀ Ideal.Quotient.mk_surjective Q [] hQ 0 := by
  simp [exteriorGenericEuler]

end MotivicTest.KoszulExteriorGenericEuler
