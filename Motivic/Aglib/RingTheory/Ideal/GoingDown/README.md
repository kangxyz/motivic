# Going down, minimal primes and finite-type base change

These local results extend Mathlib's actual `Algebra.HasGoingDown`
property. Their source owner is `Motivic.Aglib.RingTheory.Ideal.GoingDown`; the declaration namespace
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
lower local leaf `Motivic.Aglib.RingTheory.MvPolynomial.IsIntegrallyClosed` and
Mathlib's integral-normal-domain going-down theorem. `BaseChange` imports
`Polynomial`, `TensorProduct`, finite type and polynomial tensor products.
`MinimalPrimes` imports only the pinned lower
`Aglib.RingTheory.Ideal.MinimalPrime.GoingDown` leaf. This complete local
closure has no ordinary Motivic application dependency.

Current consumers include smooth normality and actual finite geometric
base-change constructions. Their host correspondence specializations consume
these candidates; they do not supply candidate prerequisites.

## Prime heights

`Motivic.Aglib.RingTheory.Ideal.GoingDown.Height`, in native `PrimeSpectrum`,
retains the actual contraction of prime ideals. Its
`height_comap_eq_of_isIntegral_of_hasGoingDown` proves equality of heights
for integral maps satisfying going down, hence for finite flat algebras. Both rings are Noetherian; neither
is required to be a domain, reduced, connected or nontrivial. This is a lower
height input for regular-principal whole zero-cycle calculations, not a change
to the stronger premises of the polynomial/base-change interfaces above.
