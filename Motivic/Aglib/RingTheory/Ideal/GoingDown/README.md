# Going down, minimal primes and finite-type base change

These local candidates extend Mathlib's actual `Algebra.HasGoingDown`
property. Their intended upstream owner is `Aglib.RingTheory.Ideal.GoingDown`;
the temporary import root is `Motivic.Aglib`, and the declaration namespace
is `Algebra.HasGoingDown` for transport/base change and `Ideal` for
minimal-prime contraction.

## Interfaces and hypotheses

- `MinimalPrimes.lean`: `Ideal.minimalPrime_under_of_goingDown` contracts
  an actual minimal prime through a supplied going-down algebra;
  `Ideal.minimalPrime_under_eq_bot_of_goingDown` identifies that contraction
  with zero when the base is a domain. The two rings retain independent
  universes. The target algebra can be nonreduced, disconnected or zero;
  no target-domain, flatness, finite-type, integrality or Noetherian premise
  is added. Contraction is exactly `Ideal.under` along `algebraMap`.

- `Equiv.lean`: `of_equivalences` transports going down across compatible
  ring equivalences of the source and target. The four commutative rings may
  occupy independent universes. The hypothesis is an equality of the actual
  composites with their algebra maps. `of_algEquiv` specializes this transport
  to an algebra equivalence with unchanged base.
- `Quotient.lean`: `quotient_map` descends supplied going down for `R → S` to
  the canonical algebra `R / I → S / IS`, for any ideal `I`. The algebra is
  `Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map`.
- `TensorProduct.lean`: `tensor_quotient` descends going down for `P → P ⊗[R] S`
  through any ideal of `P`; `tensor_of_surjective` descends it through a supplied
  surjective `R`-algebra map `P → A`. Both use the actual left-factor algebra
  maps, canonical quotient-tensor equivalence and quotient-kernel equivalence.
  The four rings retain independent universes.
- `Polynomial.lean`: `mvPolynomial_fin` proves going down after adjoining
  `Fin n` variables to an integral faithful `R`-algebra `S`, when `S` is a domain
  and `R` is integrally closed. The proof derives `IsDomain R` from faithfulness
  and uses the separate `MvPolynomial.isIntegrallyClosed_fin` theorem.
- `BaseChange.lean`: `mvPolynomial_tensor` transports polynomial going down
  through the canonical polynomial-tensor equivalence. `finiteType_baseChange`
  then proves going down for `A → A ⊗[R] S` for any finite-type `R`-algebra `A`,
  retaining precisely the integral, faithful, domain-target and normal-base
  hypotheses above. No domain, reducedness or normality is required of `A`
  or the tensor product. The rings retain independent universes.

Equivalence transport, quotient descent and the two tensor-descent results
impose no domain, nontriviality, reducedness, Noetherianity, normality,
integrality, flatness or finite-type condition. The quotient results include
the unit ideal and zero quotient rings. The polynomial and finite-type leaves
retain their stronger stated hypotheses; finite type is not finite presentation.

## Dependency direction and upstream interfaces

`Equiv` and `Quotient` import only `Mathlib.RingTheory.Ideal.GoingDown`.
`TensorProduct` imports those leaves and Mathlib's tensor-quotient interface,
without any normality or finite-type prerequisites. `Polynomial` imports the
lower candidate `Motivic.Aglib.RingTheory.MvPolynomial.IsIntegrallyClosed` and
Mathlib's integral-normal-domain going-down theorem. `BaseChange` imports
`Polynomial`, `TensorProduct`, finite type and polynomial tensor products.
`MinimalPrimes` imports only the pinned lower
`Aglib.RingTheory.Ideal.MinimalPrime.GoingDown` leaf. This complete candidate
closure has no ordinary Motivic application dependency.

At pinned Aglib revision `40af743ab794d607f566cec0c5417d8e4d02a735`,
`Aglib.RingTheory.Ideal.MinimalPrime.GoingDown` supplies the more general
`Ideal.minimalPrime_map_under_of_goingDown` for minimal primes over an
extended ideal. The new minimal-prime interfaces specialize that canonical
proof to the zero ideal rather than duplicating its going-down argument;
the domain conclusion then uses Mathlib's singleton description of minimal
primes. There is no exact duplicate of the two native interfaces in either
pinned source tree. These are distinct from the family's transport/base-change
theorems and from the already native
`Motivic.Aglib.RingTheory.FlatTorsionFreeMinimalPrimes` results, whose hypotheses
are torsion-freeness and flat scalar extension.
Pinned Mathlib supplies the native going-down property, transitivity, its
prime-spectrum criterion, flat going down and integral-normal-domain going
down. It supplies the canonical tensor equivalences and finite polynomial
presentation used here, but no duplicate of the extracted interfaces was found.

## Current consumers and verification scope

`Motivic.RingTheory.Smooth.Normal` imports only the separate polynomial
integral-closedness candidate. `Motivic.AlgebraicGeometry.Cycles.FiniteBaseChangeDominance`
and `FiniteBaseChangeGeneralizing` use `finiteType_baseChange` for actual affine
tensor-product pullbacks. These geometric applications remain downstream.

`MotivicTest.GenericDominance` is the current direct consumer of the minimal-prime
interfaces; no ordinary production leaf directly imported the old minimal-prime
source. It checks independent ring universes, contraction along the actual
algebra map, and the zero-contraction conclusion for a literal dual-number
algebra with a proved nonzero square-zero element. Its existing finite-flat
and disconnected scheme consumers remain downstream. Its focused transitive
axiom check rejects any foundation outside `propext`, `Classical.choice` and
`Quot.sound` for both extracted declarations and the named test consumers.

`MotivicTest.GoingDownEquiv` checks reverse transport and the fixed-base algebra
map specialization. `MotivicTest.GoingDownQuotient` checks the canonical quotient
map, arbitrary ideals and zero quotient rings. `MotivicTest.GoingDownBaseChange`
checks independent ring universes, unconstrained quotient/surjection descent,
polynomial normality, actual coefficient/tensor maps, and finite-type
base changes by nonreduced, disconnected and zero algebras. A focused axiom probe
covers the six declarations extracted in this cohort.

Ordinary strict incremental checks cover changed leaves and affected consumers.
They do not assert upstream acceptance or a whole-project integration result.
Historical tools, audit snapshots and verification receipts retain historical
paths and are not current evidence for this surface. There are no production
compatibility wrappers for retired paths or names. The old
`Motivic/RingTheory/GoingDown/Polynomial.lean` and `BaseChange.lean` source
leaves have been removed after their root exports and consumers were retargeted.

## Source provenance and mathematical correspondence

`MinimalPrimes.lean` is extracted from
`Motivic/RingTheory/GoingDown/MinimalPrimes.lean`, source SHA-256
`80ac76e84d87fa335aa395ad7f2a2c304812029b33be5b5fd3bdd8499be67741`.
Both old `Motivic` theorem names retain their suffixes under native `Ideal`.
Their hypotheses, two independent universes and actual contraction map are
unchanged. The first proof now reuses the pinned more general ideal theorem;
this changes no mathematical premise. The root exports now use the native interface, and the old production source
has been removed without compatibility wrappers.

Copyright, Apache 2.0 notices, contributor attribution, theorem hypotheses
and universes are preserved. The transport/base-change proof bodies are
preserved. This workspace has no Git metadata; the precise pre-extraction
sources are recorded by path and SHA-256:

- `Motivic/RingTheory/GoingDown/Equiv.lean`:
  `bbb42307a6d334af580be7bfb224009bcb667530f474c99ae39104558cfef9f4`
- `Motivic/RingTheory/GoingDown/Quotient.lean`:
  `e9480ed85615b50562f045a1b3b304b53230d2a73a347ec3501d89d044843c3b`
- `Motivic/RingTheory/GoingDown/Polynomial.lean`:
  `45bcfecc8de5aff09198f68b09c269c4ff45a4a2e380c83f0a29fbc1b98939d1`
- `Motivic/RingTheory/GoingDown/BaseChange.lean`:
  `adf1dd2b2b356e30e7ae322da32387dce5edfb681dc840cfbd22ea1c3b67ed6e`

The normality proof still inducts through the empty-variable and finite-successor
ring equivalences. Polynomial going down still derives the base domain from
the original injective algebra map before applying the normal-domain theorem.
Tensor descent still uses the original quotient, quotient-kernel and tensor
congruence maps, with their commuting squares proved on actual elements.
Finite-type base change still uses the same finite polynomial presentation and
surjective-descent proof. Module locations and native declaration names change;
none of these map constructions or mathematical premises is replaced.
