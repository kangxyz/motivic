/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulExteriorCoefficientComparison
public import Motivic.AlgebraicGeometry.Diagonal.AffineMiddleSupports
public import Motivic.AlgebraicGeometry.Intersection.ClosedSpecTor

/-!
# Actual six-factor exterior coefficient consumers

The coefficient module is the literal tensor of the three support quotients,
with the exterior quotient action. Ideals are arbitrary, including nonradical
ideals; no flatness is required for any support quotient map.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Motivic.Koszul
open scoped TensorProduct Motivic.MiddleDiagonal

namespace MotivicTest.KoszulExteriorCoefficientComparison

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

set_option backward.isDefEq.respectTransparency false in
/-- Actual support-quotient cancellation keeps the specified pairwise scalar action. -/
def actualCoefficientCancellation :
    (ModuleCat.extendScalars (R := P₀) (S := S₀) (λ₀).toRingHom).obj
        (Motivic.Intersection.specCoordinateModule (R := P₀) (A := T₀) (σ₀).toRingHom) ≅
      Motivic.Intersection.specCoordinateModule (R := S₀) (A := N₆)
        (Algebra.TensorProduct.map σ₀ (AlgHom.id k E₀)).toRingHom :=
  exteriorCoefficientIso (P := P₀) (T := T₀) (E := E₀) σ₀

set_option backward.isDefEq.respectTransparency false in
/-- The literal six-factor chain comparison for any first diagonal list. -/
def actualExteriorChainIso (t : List P₀) :
    coefficientComplex
        (Motivic.Intersection.specCoordinateModule (R := P₆) (A := N₆) (τ₀).toRingHom)
        (t.map (Algebra.TensorProduct.includeLeft : P₀ →ₐ[k] P₆)) ≅
      crossMappedComplex (ModuleCat.restrictScalars (R := P₆) (S := S₀) (ρ₀).toRingHom)
        (crossMappedComplex (ModuleCat.extendScalars (R := P₀) (S := S₀) (λ₀).toRingHom)
          (coefficientComplex
            (Motivic.Intersection.specCoordinateModule (R := P₀) (A := T₀) (σ₀).toRingHom) t)) :=
  exteriorCoefficientChainIso (P := P₀) (T := T₀) (E := E₀) (W := W₀) σ₀ q₀ t

/-- Repeated and zero equations are allowed in the actual exterior chain bridge. -/
def repeatedZeroActualExterior (a : P₀) :=
  actualExteriorChainIso k A B C D I J K [a, a, 0]

set_option backward.isDefEq.respectTransparency false in
/-- The base field supplies flatness of the actual additional-factor extension. -/
theorem actualExtensionFlat : RingHom.Flat (R := P₀) (S := S₀) (λ₀).toRingHom :=
  exteriorIncludeLeft_flat

set_option backward.isDefEq.respectTransparency false in
/-- Actual first-stage homology carries the literal six-factor ambient action. -/
def actualExteriorHomologyIso (t : List P₀) (n : ℕ) :
    (coefficientComplex
      (Motivic.Intersection.specCoordinateModule (R := P₆) (A := N₆) (τ₀).toRingHom)
      (t.map (Algebra.TensorProduct.includeLeft : P₀ →ₐ[k] P₆))).homology n ≅
    (ModuleCat.restrictScalars (R := P₆) (S := S₀) (ρ₀).toRingHom).obj
      ((ModuleCat.extendScalars (R := P₀) (S := S₀) (λ₀).toRingHom).obj
        ((coefficientComplex
          (Motivic.Intersection.specCoordinateModule
            (R := P₀) (A := T₀) (σ₀).toRingHom) t).homology n)) :=
  exteriorCoefficientHomologyIso (P := P₀) (T := T₀) (E := E₀) (W := W₀) σ₀ q₀ t n

/-- Empty first-stage lists are included in the same genuine homology comparison. -/
def emptyActualExteriorHomology (n : ℕ) :=
  actualExteriorHomologyIso k A B C D I J K [] n

end MotivicTest.KoszulExteriorCoefficientComparison
