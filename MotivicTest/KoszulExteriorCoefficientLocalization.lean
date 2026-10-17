/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulExteriorCoefficientLocalization
public import Motivic.AlgebraicGeometry.Diagonal.AffineMiddleSupports
public import Motivic.AlgebraicGeometry.Intersection.ClosedSpecTor

/-!
# Localized actual six-factor exterior homology consumers

The coefficient module is the literal tensor of the three support quotients,
with the exterior quotient action. Ideals are arbitrary, including nonradical
ideals; no flatness is required for any support quotient map.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Motivic.Koszul
open scoped TensorProduct Motivic.MiddleDiagonal

namespace MotivicTest.KoszulExteriorCoefficientLocalization

variable (k A B C D : Type u) [Field k] [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra k A] [Algebra k B] [Algebra k C] [Algebra k D]
  (I : Ideal (A ⊗[k] B)) (J : Ideal (B ⊗[k] C)) (K : Ideal (C ⊗[k] D))

local notation "P₀" => Motivic.MiddleDiagonal.ambientRing k A B C
local notation "T₀" => ((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J)
local notation "W₀" => C ⊗[k] D
local notation "E₀" => (C ⊗[k] D) ⧸ K
local notation "S₀" => P₀ ⊗[k] E₀
local notation "P₆" => P₀ ⊗[k] W₀
local notation "N₆" => T₀ ⊗[k] E₀
local notation "σ₀" => Motivic.AffineMiddle.supportRingMap k A B C I J
local notation "q₀" => Ideal.Quotient.mkₐ k K
local notation "λ₀" => (Algebra.TensorProduct.includeLeft : P₀ →ₐ[k] S₀)
local notation "ρ₀" => (Algebra.TensorProduct.map (AlgHom.id k P₀) q₀)
local notation "τ₀" => (Algebra.TensorProduct.map σ₀ q₀)

/-- Cache the canonical pair-support ring instance before the third tensor factor. -/
local instance pairSupportCommRing : CommRing T₀ := inferInstance

/-- Cache the same canonical pair-support k-algebra instance. -/
local instance pairSupportAlgebra : Algebra k T₀ := inferInstance


variable (Q : Ideal (Motivic.MiddleDiagonal.ambientRing k A B C ⊗[k]
  ((C ⊗[k] D) ⧸ K))) [Q.IsPrime]

/-- Every actual first-stage homology localizes to the tensor of localized pair
homology. The inferred target retains the exact localRingHom algebra and
quotient-localized ambient action from the proved comparison. -/
def actualLocalizedExteriorHomologyIso (t : List P₀) (n : ℕ) :=
  exteriorPrimeLocalizedHomologyIso (P := P₀) (T := T₀) (E := E₀) (W := W₀)
    σ₀ q₀ Ideal.Quotient.mk_surjective Q t n

/-- Repeated and zero equations retain all positive-degree homology terms. -/
def repeatedZeroLocalizedHomology (a : P₀) (n : ℕ) :=
  actualLocalizedExteriorHomologyIso k A B C D I J K Q [a, a, 0] n

/-- The same actual localization comparison includes an empty first-stage list. -/
def emptyLocalizedHomology (n : ℕ) :=
  actualLocalizedExteriorHomologyIso k A B C D I J K Q [] n

end MotivicTest.KoszulExteriorCoefficientLocalization
