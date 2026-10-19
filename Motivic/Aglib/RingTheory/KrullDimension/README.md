# Krull dimension of finite flat polynomial algebras

[PolynomialFiniteFlatComponents](PolynomialFiniteFlatComponents.lean) uses
native ring, ideal and `PrimeSpectrum` namespaces. For commutative rings `R,A`
with an integral `R`-algebra structure, `ringKrullDim_le_of_isIntegral` gives
`ringKrullDim A ≤ ringKrullDim R`; the structural map need not be injective,
and neither ring is required to be nontrivial.

For a field `K` and commutative `K[t]`-algebra `A`, assume
`Algebra.IsIntegral (Polynomial K) A` and
`Module.IsTorsionFree (Polynomial K) A`.
`Ideal.exists_prime_gt_of_mem_minimalPrimes_polynomial` gives a strict prime
specialization above every minimal prime `q` of `A`.
`Ideal.ringKrullDim_quotient_eq_one_of_mem_minimalPrimes_polynomial` therefore
identifies `ringKrullDim (A ⧸ q)` with one.
`PrimeSpectrum.topologicalKrullDim_zeroLocus_eq_ringKrullDim_quotient`
identifies the dimension of the actual zero locus with that of the quotient,
including nilpotent or zero quotients. Together these give
`PrimeSpectrum.topologicalKrullDim_eq_one_of_mem_irreducibleComponents_polynomial`.

`PrimeSpectrum.topologicalKrullDim_eq_one_of_mem_irreducibleComponents_finite_flat_polynomial`
specializes to a finite flat `K[t]`-algebra: every irreducible component of
`Spec A` has dimension one. Reducedness, connectedness, nontriviality and
positive rank are not assumed; the component assertion is vacuous for the zero
algebra. The [projective-line component theorem](../../AlgebraicGeometry/ProjectiveLine/README.md)
uses this exact affine algebra and its structural scalar action on each whole
chart. Intended upstream module:
`Aglib.RingTheory.KrullDimension.PolynomialFiniteFlatComponents`.
