/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.MvPolynomial.IsIntegrallyClosed
public import Mathlib.RingTheory.IntegralClosure.GoingDown

/-!
# Going down for polynomial extensions of normal domains

An integral inclusion of an integrally closed ring into a domain satisfies
going down after adjoining finitely many variables on both sides. Faithfulness
derives the base domain hypothesis; polynomial normality is proved separately.

## Upstream candidate

Intended upstream module: `Aglib.RingTheory.Ideal.GoingDown.Polynomial`.
The two rings may occupy independent universes. The actual polynomial algebra
uses `MvPolynomial.algebraMvPolynomial`, with its original coefficient map.
The current consumer is `Motivic.Aglib.RingTheory.Ideal.GoingDown.BaseChange`.

Extracted from `Motivic.RingTheory.GoingDown.Polynomial`, source SHA-256
`45bcfecc8de5aff09198f68b09c269c4ff45a4a2e380c83f0a29fbc1b98939d1`.
-/

@[expose] public section

universe u v

namespace Algebra.HasGoingDown

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- An integral inclusion of a normal ring into a domain satisfies going down
after adjoining finitely many variables. Normality of the polynomial base
is derived, and the target polynomial ring is genuinely a domain. -/
theorem mvPolynomial_fin [Algebra R S] [IsDomain S] [FaithfulSMul R S]
    [Algebra.IsIntegral R S] [IsIntegrallyClosed R] (n : ℕ) :
    Algebra.HasGoingDown (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) S) := by
  have : IsDomain R := (FaithfulSMul.algebraMap_injective R S).isDomain _
  have := MvPolynomial.isIntegrallyClosed_fin (R := R) n
  infer_instance


end Algebra.HasGoingDown
