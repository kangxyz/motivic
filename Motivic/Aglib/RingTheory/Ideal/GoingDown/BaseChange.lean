/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Ideal.GoingDown.Polynomial
public import Motivic.Aglib.RingTheory.Ideal.GoingDown.TensorProduct
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Finite-type base change of integral inclusions of normal domains

An integral inclusion of an integrally closed ring into a domain satisfies
going down after base change by any finite-type algebra. Polynomial going down
is transported to the actual tensor product, then descended through a finite
polynomial presentation. The base-change algebra and tensor product need not
be domains, reduced or normal.

## Upstream candidate

Intended upstream module: `Aglib.RingTheory.Ideal.GoingDown.BaseChange`.
The base, target and base-change algebra may occupy independent universes.
The original inclusion retains faithfulness, integrality, integral closedness
of the base and the domain hypothesis on the target. The current consumers are
`Motivic.AlgebraicGeometry.Cycles.FiniteBaseChangeDominance` and
`Motivic.AlgebraicGeometry.Cycles.FiniteBaseChangeGeneralizing`.

Extracted from `Motivic.RingTheory.GoingDown.BaseChange`, source SHA-256
`adf1dd2b2b356e30e7ae322da32387dce5edfb681dc840cfbd22ea1c3b67ed6e`.
-/

@[expose] public section

open scoped TensorProduct

universe u v x

namespace Algebra.HasGoingDown

variable {R : Type u} {S : Type v} {A : Type x}
  [CommRing R] [CommRing S] [CommRing A]

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- The polynomial tensor product is identified with the actual polynomial
extension before applying normal-domain going down. -/
theorem mvPolynomial_tensor [Algebra R S] [IsDomain S] [FaithfulSMul R S]
    [Algebra.IsIntegral R S] [IsIntegrallyClosed R] (n : ℕ) :
    Algebra.HasGoingDown (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R ⊗[R] S) := by
  have := mvPolynomial_fin (R := R) (S := S) n
  let e := (Algebra.TensorProduct.comm R (MvPolynomial (Fin n) R) S).trans
    ((MvPolynomial.algebraTensorAlgEquiv R S).restrictScalars R)
  apply Algebra.HasGoingDown.of_equivalences (RingEquiv.refl (MvPolynomial (Fin n) R))
    e.symm.toRingEquiv
  apply RingHom.ext
  intro p
  change e.symm (MvPolynomial.map (algebraMap R S) p) = p ⊗ₜ[R] (1 : S)
  simp [e]

/-- An integral inclusion of a normal ring into a domain satisfies going down
after base change by any finite-type algebra. No domain, reducedness, or
normality assumption is made on the algebra or the resulting tensor product. -/
theorem finiteType_baseChange [Algebra R S] [IsDomain S] [FaithfulSMul R S]
    [Algebra.IsIntegral R S] [IsIntegrallyClosed R] [Algebra R A] [Algebra.FiniteType R A] :
    Algebra.HasGoingDown A (A ⊗[R] S) := by
  obtain ⟨n, f, hf⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'').mp
    (inferInstance : Algebra.FiniteType R A)
  have := mvPolynomial_tensor (R := R) (S := S) n
  exact tensor_of_surjective (S := S) f hf


end Algebra.HasGoingDown
