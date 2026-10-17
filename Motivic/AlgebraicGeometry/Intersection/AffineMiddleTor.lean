/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.TorComparison.SupportModulesMiddle
public import Motivic.AlgebraicGeometry.Intersection.ClosedSpecComparison
public import Motivic.Algebra.Homology.TorComparison.AmbientLength

/-!
# Actual affine middle-diagonal stalk Tor

The constructed coordinate comparison is localized at the actual common prime.
The two closed-source bridges then identify actual scheme stalk Tor. Restriction
uses the literal stalk map of the middle-diagonal inclusion, whose surjectivity
is proved from the literal local quotient map. The left pulled support remains
the coefficient and the right pulled support remains the resolved source.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency true

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct Motivic.MiddleDiagonal

universe u

namespace Motivic.Intersection

namespace AffineMiddleTor

variable (k A B C : Type u) [Field k] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]

/-- The literal ring of the left support pulled to the triple product. -/
abbrev leftRing (I : Ideal (A ⊗[k] B)) :=
  (MiddleDiagonal.tripleRing k A B C) ⊗[A ⊗[k] B] ((A ⊗[k] B) ⧸ I)

/-- The literal ring of the right support uses the specified right scalar map. -/
abbrev rightRing (J : Ideal (B ⊗[k] C)) :=
  letI : Algebra (B ⊗[k] C) (MiddleDiagonal.tripleRing k A B C) :=
    (MiddleDiagonal.rightMap k A B C).toRingHom.toAlgebra
  (MiddleDiagonal.tripleRing k A B C) ⊗[B ⊗[k] C] ((B ⊗[k] C) ⧸ J)

/-- Coordinate map of the actual left pulled-back closed support. -/
def leftMap (I : Ideal (A ⊗[k] B)) :
    MiddleDiagonal.tripleRing k A B C →+* leftRing k A B C I :=
  Algebra.TensorProduct.includeLeftRingHom

/-- Coordinate map of the actual right pulled-back closed support. -/
def rightMap (J : Ideal (B ⊗[k] C)) :
    MiddleDiagonal.tripleRing k A B C →+* rightRing k A B C J :=
  letI : Algebra (B ⊗[k] C) (MiddleDiagonal.tripleRing k A B C) :=
    (MiddleDiagonal.rightMap k A B C).toRingHom.toAlgebra
  Algebra.TensorProduct.includeLeftRingHom

/-- The actual left pulled-support coordinate map is surjective. -/
theorem leftMap_surjective (I : Ideal (A ⊗[k] B)) :
    Function.Surjective (leftMap k A B C I) :=
  Algebra.TensorProduct.includeLeft_surjective (A ⊗[k] B)
    (MiddleDiagonal.tripleRing k A B C) Ideal.Quotient.mk_surjective

/-- The actual right pulled-support coordinate map is surjective. -/
theorem rightMap_surjective (J : Ideal (B ⊗[k] C)) :
    Function.Surjective (rightMap k A B C J) := by
  let : Algebra (B ⊗[k] C) (MiddleDiagonal.tripleRing k A B C) :=
    (MiddleDiagonal.rightMap k A B C).toRingHom.toAlgebra
  exact Algebra.TensorProduct.includeLeft_surjective (B ⊗[k] C)
    (MiddleDiagonal.tripleRing k A B C) Ideal.Quotient.mk_surjective

/-- The literal quotient ring map, with its two coordinate rings fixed. -/
def diagonalRingMap :
    MiddleDiagonal.ambientRing k A B C →+* MiddleDiagonal.tripleRing k A B C :=
  (MiddleDiagonal.quotientMap k A B C).toRingHom

/-- The literal product-support quotient, with its coordinate rings fixed. -/
def productSupportRingMap (I : Ideal (A ⊗[k] B)) (J : Ideal (B ⊗[k] C)) :
    MiddleDiagonal.ambientRing k A B C →+* (((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J)) :=
  (AffineMiddle.supportRingMap k A B C I J).toRingHom

/-- The actual diagonal scheme map with its coordinate rings fixed explicitly. -/
abbrev diagonalSpecMap : Spec (CommRingCat.of (MiddleDiagonal.tripleRing k A B C)) ⟶
    Spec (CommRingCat.of (MiddleDiagonal.ambientRing k A B C)) :=
  Spec.map (CommRingCat.ofHom (R := MiddleDiagonal.ambientRing k A B C)
    (S := MiddleDiagonal.tripleRing k A B C) (diagonalRingMap k A B C))

/-- The actual product-support inclusion with explicitly fixed coordinate rings. -/
abbrev supportSpecMap (I : Ideal (A ⊗[k] B)) (J : Ideal (B ⊗[k] C)) :
    Spec (CommRingCat.of (((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J))) ⟶
      Spec (CommRingCat.of (MiddleDiagonal.ambientRing k A B C)) :=
  Spec.map (CommRingCat.ofHom (R := MiddleDiagonal.ambientRing k A B C)
    (S := ((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J))
    (productSupportRingMap k A B C I J))

/-- The actual left pulled-support scheme map with the literal coordinate action. -/
abbrev leftSpecMap (I : Ideal (A ⊗[k] B)) :
    Spec (CommRingCat.of (leftRing k A B C I)) ⟶
      Spec (CommRingCat.of (MiddleDiagonal.tripleRing k A B C)) :=
  Spec.map (CommRingCat.ofHom (R := MiddleDiagonal.tripleRing k A B C)
    (S := leftRing k A B C I) (leftMap k A B C I))

/-- The actual right pulled-support scheme map with the literal coordinate action. -/
abbrev rightSpecMap (J : Ideal (B ⊗[k] C)) :
    Spec (CommRingCat.of (rightRing k A B C J)) ⟶
      Spec (CommRingCat.of (MiddleDiagonal.tripleRing k A B C)) :=
  Spec.map (CommRingCat.ofHom (R := MiddleDiagonal.tripleRing k A B C)
    (S := rightRing k A B C J) (rightMap k A B C J))

variable (I : Ideal (A ⊗[k] B)) (J : Ideal (B ⊗[k] C))

/-- Ambient-coordinate Tor, before localization, in its prescribed argument order. -/
def ambientCoordinateTor (n : ℕ) : ModuleCat.{u} (MiddleDiagonal.ambientRing k A B C) :=
  closedCoordinateTor (R := MiddleDiagonal.ambientRing k A B C)
    (A := ((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J))
    (B := MiddleDiagonal.tripleRing k A B C)
    (productSupportRingMap k A B C I J)
    (diagonalRingMap k A B C) n

/-- Actual pulled-support coordinate Tor, with the left support first. -/
def pulledCoordinateTor (n : ℕ) : ModuleCat.{u} (MiddleDiagonal.tripleRing k A B C) :=
  closedCoordinateTor (R := MiddleDiagonal.tripleRing k A B C)
    (A := leftRing k A B C I) (B := rightRing k A B C J)
    (leftMap k A B C I) (rightMap k A B C J) n

/-- The coordinate comparison is the genuine constructed middle-diagonal Tor isomorphism. -/
def coordinateTorIso (n : ℕ) :
    ambientCoordinateTor k A B C I J n ≅
      (ModuleCat.restrictScalars (diagonalRingMap k A B C)).obj
        (pulledCoordinateTor k A B C I J n) :=
  TorComparison.SupportModules.middleSupportTorIso k A B C I J n

/-- Localizing the genuine support comparison retains the literal local quotient
scalar restriction for arbitrary ideals and every degree. -/
def localizedSupportTorIso (q : PrimeSpectrum (MiddleDiagonal.tripleRing k A B C))
    (n : ℕ) :
    primeLocalizedModule
      (q.comap (diagonalRingMap k A B C)).asIdeal
      (ambientCoordinateTor k A B C I J n) ≅
    (ModuleCat.restrictScalars (specSourceLocalMap (R := MiddleDiagonal.ambientRing k A B C)
      (A := MiddleDiagonal.tripleRing k A B C)
      (diagonalRingMap k A B C) q)).obj
      (primeLocalizedModule q.asIdeal (pulledCoordinateTor k A B C I J n)) :=
  closedLocalizedComparisonIso (R := MiddleDiagonal.ambientRing k A B C)
    (S := MiddleDiagonal.tripleRing k A B C) (diagonalRingMap k A B C)
    (MiddleDiagonal.quotientMap_surjective k A B C) q
    (ambientCoordinateTor k A B C I J n) (pulledCoordinateTor k A B C I J n)
    (coordinateTorIso k A B C I J n)

variable (l : PrimeSpectrum (leftRing k A B C I))
  (r : PrimeSpectrum (rightRing k A B C J))
  (t : PrimeSpectrum (((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J)))
  (hq : r.comap (rightMap k A B C J) = l.comap (leftMap k A B C I))
  (hp : (r.comap (rightMap k A B C J)).comap (diagonalRingMap k A B C) =
    t.comap (productSupportRingMap k A B C I J))

/-- Actual triple-product stalk Tor of the two pulled supports, coefficient first. -/
def pulledStalkTor (n : ℕ) :=
  let tor := @closedStalkTor (MiddleDiagonal.tripleRing k A B C)
    (rightRing k A B C J) (leftRing k A B C I) inferInstance inferInstance inferInstance
    (rightMap k A B C J) r (leftMap k A B C I) l
  tor hq n

/-- The actual affine intersection comparison in every degree. Its only
point hypotheses say that the actual support points have the same images.
The module comparison and the literal quotient-stalk action are constructed. -/
def stalkTorIso (n : ℕ) :=
  let compare := @closedStalkComparisonIso (MiddleDiagonal.ambientRing k A B C)
    (MiddleDiagonal.tripleRing k A B C)
    (((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J))
    (leftRing k A B C I) (rightRing k A B C J)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (diagonalRingMap k A B C)
    (MiddleDiagonal.quotientMap_surjective k A B C)
    (productSupportRingMap k A B C I J)
    (AffineMiddle.supportRingMap_surjective k A B C I J)
    (leftMap k A B C I) (leftMap_surjective k A B C I)
    (rightMap k A B C J) (rightMap_surjective k A B C J) l r t
  compare hq hp n (coordinateTorIso k A B C I J n)

/-- Actual four-factor stalk Tor, extracted from the constructed comparison's source.
This avoids expanding the nested tensor coordinate maps when fixing its local action. -/
def ambientStalkTor (n : ℕ) :=
  let source {R : Type u} [Ring R] {M N : ModuleCat.{u} R} (_ : M ≅ N) := M
  source (stalkTorIso k A B C I J l r t hq hp n)

include hq hp in
/-- Extended-natural local lengths agree, including potentially infinite length.
This is a local stalk result, not a statement about global coordinate length. -/
theorem stalkTor_length (n : ℕ) :
    Module.length (ambientStalk
      (diagonalSpecMap k A B C)
      (r.comap (rightMap k A B C J))) (ambientStalkTor k A B C I J l r t hq hp n) =
      Module.length (ambientStalk (rightSpecMap k A B C J) r)
        (pulledStalkTor k A B C I J l r hq n) :=
  @closedStalkComparison_length (MiddleDiagonal.ambientRing k A B C)
    (MiddleDiagonal.tripleRing k A B C)
    (((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J))
    (leftRing k A B C I) (rightRing k A B C J)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (diagonalRingMap k A B C) (MiddleDiagonal.quotientMap_surjective k A B C)
    (productSupportRingMap k A B C I J) (AffineMiddle.supportRingMap_surjective k A B C I J)
    (leftMap k A B C I) (leftMap_surjective k A B C I)
    (rightMap k A B C J) (rightMap_surjective k A B C J) l r t hq hp n
    (coordinateTorIso k A B C I J n)

include hq hp in
/-- Finite local Tor length and finite degree support transfer only from genuine
input evidence; no universal finite-length claim is made about support modules. -/
theorem stalkTor_finiteLengthSupport_iff :
    LengthEuler.FiniteLengthSupport (ambientStalkTor k A B C I J l r t hq hp) ↔
      LengthEuler.FiniteLengthSupport (pulledStalkTor k A B C I J l r hq) := by
  have hlen := funext (stalkTor_length k A B C I J l r t hq hp)
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro n
      rw [← stalkTor_length k A B C I J l r t hq hp n]
      exact h.finite_length n
    · simpa only [hlen] using h.finite_support
  · intro h
    refine ⟨?_, ?_⟩
    · intro n
      rw [stalkTor_length k A B C I J l r t hq hp n]
      exact h.finite_length n
    · simpa only [hlen] using h.finite_support

/-- Genuine finite local Tor Euler sums agree for every chosen sign convention. -/
theorem stalkTor_signedLengthSum (sign : ℕ → ℤ)
    (h : LengthEuler.FiniteLengthSupport (ambientStalkTor k A B C I J l r t hq hp)) :
    LengthEuler.signedLengthSum (ambientStalkTor k A B C I J l r t hq hp) sign h =
      LengthEuler.signedLengthSum (pulledStalkTor k A B C I J l r hq) sign
        ((stalkTor_finiteLengthSupport_iff k A B C I J l r t hq hp).mp h) := by
  unfold LengthEuler.signedLengthSum
  apply finsum_congr
  intro n
  simp only [LengthEuler.integerLength, stalkTor_length k A B C I J l r t hq hp n]

end AffineMiddleTor

end Motivic.Intersection
