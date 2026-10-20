/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Polynomial.IsIntegral

/-!
# Integral closedness of finite-variable polynomial rings

A polynomial ring in finitely many numbered variables over an integrally
closed domain is integrally closed. The induction uses the actual empty-variable
and `MvPolynomial.finSuccEquiv` ring equivalences and the univariate instance.

## Upstream candidate

Intended upstream module: `Aglib.RingTheory.MvPolynomial.IsIntegrallyClosed`.
The coefficient ring has arbitrary universe and retains both `IsDomain` and
`IsIntegrallyClosed`. Current consumers are polynomial going down in
`Motivic.Aglib.RingTheory.Ideal.GoingDown.Polynomial` and smooth normality in
`Motivic.Aglib.RingTheory.Smooth.Normal`.

Extracted from `Motivic.RingTheory.GoingDown.Polynomial`, source SHA-256
`45bcfecc8de5aff09198f68b09c269c4ff45a4a2e380c83f0a29fbc1b98939d1`.
-/

@[expose] public section

universe u

namespace MvPolynomial

variable {R : Type u} [CommRing R]

/-- A polynomial ring in finitely many numbered variables over a normal
domain is integrally closed. -/
theorem isIntegrallyClosed_fin [IsDomain R] [IsIntegrallyClosed R]
    (n : ℕ) : IsIntegrallyClosed (MvPolynomial (Fin n) R) := by
  induction n with
  | zero => exact IsIntegrallyClosed.of_equiv (MvPolynomial.isEmptyRingEquiv R (Fin 0)).symm
  | succ n ih =>
    have := ih
    exact IsIntegrallyClosed.of_equiv (MvPolynomial.finSuccEquiv R n).symm.toRingEquiv

end MvPolynomial
