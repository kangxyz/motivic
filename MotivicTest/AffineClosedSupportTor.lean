/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Intersection.AffineClosedSupportTor

/-! # Actual arbitrary-quotient and finite-Euler closed-support consumers -/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Motivic.MotivicTest.AffineClosedSupportTor

open AffineMiddle AffineMiddle.ClosedSupport Intersection

variable (k A B C : Type u) [Field k] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]

/-- Arbitrary quotient ideals, including nonradical ideals, have the actual comparison.
Neither quotient support is required to be an integral or finite correspondence. -/
theorem arbitraryQuotientComparison (I : Ideal (A ⊗[k] B)) (J : Ideal (B ⊗[k] C))
    (d : correspondenceTripleProduct (structureMap k A) (structureMap k B) (structureMap k C))
    (t : ClosedSupport.supportProduct k A B C (leftSupportMap k A B I) (rightSupportMap k B C J))
    (hp : correspondenceTripleInclusion (structureMap k A) (structureMap k B)
      (structureMap k C) d =
      ClosedSupport.supportInclusion k A B C (leftSupportMap k A B I) (rightSupportMap k B C J) t) :
    ∃ l : leftPulled k A B C (leftSupportMap k A B I),
    ∃ r : rightPulled k A B C (rightSupportMap k B C J),
    ∃ hl : leftPulledInclusion k A B C (leftSupportMap k A B I) l = d,
    ∃ hr : rightPulledInclusion k A B C (rightSupportMap k B C J) r = d,
    ∀ n : ℕ,
      Module.length (ambientStalk
        (correspondenceTripleInclusion (structureMap k A) (structureMap k B) (structureMap k C)) d)
        (ClosedSupport.ambientTor k A B C (leftSupportMap k A B I) (rightSupportMap k B C J)
          d t hp n) =
      Module.length (ambientStalk (rightPulledInclusion k A B C (rightSupportMap k B C J)) r)
        (pulledTor k A B C (leftSupportMap k A B I) (rightSupportMap k B C J)
          l r (hr.trans hl.symm) n) :=
  exists_stalkTor_length_eq_pulled k A B C (leftSupportMap k A B I) (rightSupportMap k B C J)
    d t hp

/-- Genuine finite higher-Tor evidence yields the full signed coefficient on the
constructed pulled-support points; higher degrees are not discarded. -/
theorem actualFiniteEuler {D E : Scheme.{u}}
    (a : D ⟶ leftProduct k A B) (b : E ⟶ rightProduct k B C)
    [IsClosedImmersion a] [IsClosedImmersion b]
    (d : correspondenceTripleProduct (structureMap k A) (structureMap k B) (structureMap k C))
    (t : ClosedSupport.supportProduct k A B C a b)
    (hp : correspondenceTripleInclusion (structureMap k A) (structureMap k B)
      (structureMap k C) d = ClosedSupport.supportInclusion k A B C a b t)
    (hfin : LengthEuler.FiniteLengthSupport (ClosedSupport.ambientTor k A B C a b d t hp)) :
    ∃ l : leftPulled k A B C a, ∃ r : rightPulled k A B C b,
    ∃ hl : leftPulledInclusion k A B C a l = d,
    ∃ hr : rightPulledInclusion k A B C b r = d,
    ∃ hfin' : LengthEuler.FiniteLengthSupport (pulledTor k A B C a b l r (hr.trans hl.symm)),
    ∀ sign : ℕ → ℤ,
      LengthEuler.signedLengthSum (ClosedSupport.ambientTor k A B C a b d t hp) sign hfin =
      LengthEuler.signedLengthSum (pulledTor k A B C a b l r (hr.trans hl.symm)) sign hfin' := by
  obtain ⟨l, r, hl, hr, hlen⟩ := exists_stalkTor_length_eq_pulled k A B C a b d t hp
  have hfin' : LengthEuler.FiniteLengthSupport
      (pulledTor k A B C a b l r (hr.trans hl.symm)) := by
    refine ⟨?_, ?_⟩
    · intro n
      rw [← hlen n]
      exact hfin.finite_length n
    · have he := funext hlen
      simpa only [he] using hfin.finite_support
  refine ⟨l, r, hl, hr, hfin', fun sign ↦ ?_⟩
  unfold LengthEuler.signedLengthSum
  apply finsum_congr
  intro n
  simp only [LengthEuler.integerLength, hlen n]

end Motivic.MotivicTest.AffineClosedSupportTor
