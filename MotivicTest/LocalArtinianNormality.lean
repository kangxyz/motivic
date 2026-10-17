/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.RingTheory.IntegralClosure.LocalArtinian

/-!
# Consumers of local Artinian normality descent

The quantified consumer has no independent nontriviality or faithfulness
hypothesis on the ambient algebra. The self-algebra test covers reduced local
Artinian rings, and the product test detects the nontrivial idempotents that
prevent a disconnected algebra from being relatively integrally closed over
a local ring. The field parameter is arbitrary, with no perfectness hypothesis.
-/

@[expose] public section

universe u v

namespace MotivicTest.LocalArtinianNormality

/-- Relative normality yields both domainhood and integral closedness, without
assuming that the ambient algebra is nontrivial or a domain. -/
theorem descent_without_ambient_nontriviality (C : Type u) (D : Type v)
    [CommRing C] [CommRing D] [Algebra C D] [IsLocalRing C]
    [IsIntegrallyClosedIn C D] [IsReduced D] [IsArtinianRing D] :
    IsDomain C ∧ IsIntegrallyClosed C :=
  Motivic.normalDomain_of_local_integrallyClosedIn_artinian C D

/-- The result recovers normality for reduced local Artinian rings. -/
theorem self_algebra (C : Type u) [CommRing C] [IsLocalRing C]
    [IsReduced C] [IsArtinianRing C] : IsDomain C ∧ IsIntegrallyClosed C :=
  Motivic.normalDomain_of_local_integrallyClosedIn_artinian C C

/-- An arbitrary field satisfies the result over itself. -/
theorem arbitrary_field (k : Type u) [Field k] :
    IsDomain k ∧ IsIntegrallyClosed k :=
  Motivic.normalDomain_of_local_integrallyClosedIn_artinian k k

/-- The diagonal scalar map into two copies of a field cannot be relatively
integrally closed: its nontrivial coordinate idempotent would have to descend. -/
theorem product_not_integrallyClosedIn (k : Type u) [Field k] :
    ¬ IsIntegrallyClosedIn k (k × k) := by
  intro h
  have := h
  have he : IsIdempotentElem ((1, 0) : k × k) := by
    simp [IsIdempotentElem]
  rcases Motivic.eq_zero_or_one_of_local_integrallyClosedIn (C := k) he with hz | ho
  · have hz' := congrArg Prod.fst hz
    simp at hz'
  · have ho' := congrArg Prod.snd ho
    simp at ho'

/-- A trivial ambient algebra cannot satisfy relative integral closedness
of a local scalar ring, because relative integral closedness includes injection. -/
theorem trivial_target_not_integrallyClosedIn (C : Type u) (D : Type v)
    [CommRing C] [CommRing D] [Algebra C D] [IsLocalRing C] [Subsingleton D] :
    ¬ IsIntegrallyClosedIn C D := by
  intro h
  have := h
  have hinj := IsIntegralClosure.algebraMap_injective C C D
  exact zero_ne_one (hinj (Subsingleton.elim _ _))

end MotivicTest.LocalArtinianNormality
