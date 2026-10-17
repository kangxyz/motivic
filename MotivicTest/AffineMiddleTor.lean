/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Intersection.AffineMiddleTor

/-! # Consumers of the actual local middle-diagonal intersection comparison -/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Motivic.Intersection
open scoped TensorProduct Motivic.MiddleDiagonal

universe u

namespace Motivic.MotivicTest.AffineMiddleTor

open Intersection.AffineMiddleTor

variable (k A B C : Type u) [Field k] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]
  (I : Ideal (A ⊗[k] B)) (J : Ideal (B ⊗[k] C))
  (l : PrimeSpectrum (leftRing k A B C I))
  (r : PrimeSpectrum (rightRing k A B C J))
  (t : PrimeSpectrum (((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J)))
  (hq : r.comap (rightMap k A B C J) = l.comap (leftMap k A B C I))
  (hp : (r.comap (rightMap k A B C J)).comap (diagonalRingMap k A B C) =
    t.comap (productSupportRingMap k A B C I J))

/-- The actual local comparison has an inverse in the category with literal restricted scalars. -/
theorem actualInverse (n : ℕ) :
    (stalkTorIso k A B C I J l r t hq hp n).hom ≫
      (stalkTorIso k A B C I J l r t hq hp n).inv = 𝟙 _ :=
  (stalkTorIso k A B C I J l r t hq hp n).hom_inv_id

/-- Genuine finite support on the actual ambient stalk Tor transfers to the pulled supports. -/
theorem transferActualFiniteSupport
    (h : LengthEuler.FiniteLengthSupport (ambientStalkTor k A B C I J l r t hq hp)) :
    LengthEuler.FiniteLengthSupport (pulledStalkTor k A B C I J l r hq) :=
  (stalkTor_finiteLengthSupport_iff k A B C I J l r t hq hp).mp h

/-- The usual alternating local Tor coefficient follows from actual finite-length evidence. -/
theorem actualAlternatingCoefficient
    (h : LengthEuler.FiniteLengthSupport (ambientStalkTor k A B C I J l r t hq hp)) :
    LengthEuler.signedLengthSum (ambientStalkTor k A B C I J l r t hq hp)
      (fun n ↦ (-1 : ℤ) ^ n) h =
    LengthEuler.signedLengthSum (pulledStalkTor k A B C I J l r hq)
      (fun n ↦ (-1 : ℤ) ^ n) (transferActualFiniteSupport k A B C I J l r t hq hp h) :=
  stalkTor_signedLengthSum k A B C I J l r t hq hp _ h

end Motivic.MotivicTest.AffineMiddleTor
