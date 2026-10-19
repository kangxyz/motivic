/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Smooth.Normal
public import Mathlib.RingTheory.Etale.Pi

/-!
# Consumers of smooth local normality over normal domains and fields

The base normal domain is arbitrary, and the field specializations contain
no perfectness assumption.
Neither the prime-local statement nor its disconnected and empty-algebra
consumers requires a global domain hypothesis.
-/

@[expose] public section

universe u v

namespace Motivic.MotivicTest.SmoothNormal
open _root_.Algebra.Smooth

example (R : Type u) (A : Type v) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing A] [Algebra R A] [Algebra.Smooth R A] (q : Ideal A) [q.IsPrime] :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) :=
  normalDomain_localizationAtPrime_of_smooth R A q

example (R : Type u) (A : Type v) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing A] [Algebra R A] [Algebra.Smooth R A] [IsDomain A] : IsIntegrallyClosed A :=
  isIntegrallyClosed_of_smooth R A

example (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]
    [Algebra.Smooth k A] (q : Ideal A) [q.IsPrime] :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) :=
  normalDomain_localizationAtPrime_of_smooth_field k A q

example (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]
    [Algebra.Smooth k A] [IsDomain A] : IsIntegrallyClosed A :=
  isIntegrallyClosed_of_smooth_field k A

example (k : Type u) [Field k] (q : Ideal (Fin 2 → k)) [q.IsPrime] :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) :=
  normalDomain_localizationAtPrime_of_smooth_field k (Fin 2 → k) q

example (k : Type u) [Field k] (q : Ideal (Fin 0 → k)) [q.IsPrime] :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) :=
  normalDomain_localizationAtPrime_of_smooth_field k (Fin 0 → k) q

end Motivic.MotivicTest.SmoothNormal
