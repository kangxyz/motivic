/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.RingTheory.Etale.IntegralClosure
public import Mathlib.RingTheory.Etale.Pi
public import Mathlib.Algebra.Ring.Fin

/-!
# Consumers of relative integral closure and étale local normality

These examples retain an arbitrary normal domain as base and do not assume
that an étale algebra is a domain. An arbitrary field's disconnected square
and the zero algebra are included as interface checks.
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace Motivic.MotivicTest.EtaleIntegralClosure

example (R : Type u) (C : Type v) [CommRing R] [IsDomain R] [CommRing C]
    [Algebra R C] [Algebra.EssFiniteType R C] [Algebra.FormallyUnramified R C] :
    IsReduced (C ⊗[R] FractionRing R) ∧ IsArtinianRing (C ⊗[R] FractionRing R) :=
  ⟨isReduced_tensorProduct_fractionRing_of_formallyUnramified R C,
    isArtinianRing_tensorProduct_fractionRing_of_formallyUnramified R C⟩

example (R : Type u) (S : Type v) [CommRing R] [IsIntegrallyClosed R]
    [CommRing S] [Algebra R S] [Algebra.Etale R S] (q : Ideal S) [q.IsPrime] :
    IsIntegrallyClosedIn (Localization.AtPrime q)
      (Localization.AtPrime q ⊗[R] FractionRing R) :=
  isIntegrallyClosedIn_generic_localizationAtPrime_of_etale R S q

example (R : Type u) (S : Type v) [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.Etale R S] (q : Ideal S) [q.IsPrime] :
    Function.Injective (algebraMap (Localization.AtPrime q)
      (Localization.AtPrime q ⊗[R] FractionRing R)) :=
  algebraMap_tensorProduct_fractionRing_injective_of_flat R _

example (R : Type u) (S : Type v) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing S] [Algebra R S] [Algebra.Etale R S] (q : Ideal S) [q.IsPrime] :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) :=
  normalDomain_localizationAtPrime_of_etale R S q

example (k : Type u) [Field k] (q : Ideal (k × k)) [q.IsPrime] :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  let e : (Fin 2 → k) ≃ₐ[k] k × k :=
    { RingEquiv.piFinTwo (fun _ => k) with commutes' _ := rfl }
  have : Algebra.Etale k (k × k) := Algebra.Etale.of_equiv e
  exact normalDomain_localizationAtPrime_of_etale k (k × k) q

example (k : Type u) [Field k] (q : Ideal (Fin 0 → k)) [q.IsPrime] :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) :=
  normalDomain_localizationAtPrime_of_etale k (Fin 0 → k) q

end Motivic.MotivicTest.EtaleIntegralClosure
