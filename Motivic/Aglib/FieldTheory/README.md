# Reusable field-theory results

These local `Motivic.Aglib` modules use ordinary mathematical namespaces. Their
placement records reusable algebraic foundations, not upstream acceptance.
Milnor groups, polynomial norms, and motivic-specific consumers remain outside
this directory.

## Rational functions

- `RatFuncInversion.lean` constructs the actual involutive algebra equivalence
  `X ↦ X⁻¹`, with literal constant and variable formulas.
- `RatFuncReverse.lean` expresses inversion of a polynomial using its reversal
  and the original natural degree, including zero and constant polynomials.
- `RatFuncCoefficientMap.lean` proves that the actual coefficient extension
  fixes the variable and commutes with inversion. It uses the polynomial-local
  residue base-change maps from the neighboring ring-theory modules.

## Finite Sylow fixed fields

`SylowFixedField.lean` has Mathlib-only imports and declarations in
`IntermediateField`.

1. In a finite extension `M/S` of degree `p^r`, a root of a nonzero polynomial
   over the original base of natural degree below the prime `p` belongs to `S`.
   Its minimal degree is positive, divides `p^r`, and is below `p`, so is one.
2. Any polynomial of degree below `p` that splits in the specified field `M`
   consequently splits in `S`. Zero is handled explicitly; constants are included.
3. A Sylow `p`-subgroup of the automorphism group of a finite extension has an
   actual prime-power extension above its fixed field. Galoisness over the
   original base is not needed for this assertion or the resulting splitting.
4. When `M/k` is finite Galois, the fixed field has degree prime to `p` over `k`.
   A supplied finite family of small-degree polynomials already split in `M`
   therefore has a simultaneous finite prime-to-`p` splitting subfield.

The underlying Mathlib APIs are finite Galois correspondence, Sylow index
coprimality, finite p-group cardinality, minimal-polynomial degree divisibility,
and splitting descent to intermediate fields. The module combines these APIs;
it does not replace their definitions or introduce additional axioms.

The hypotheses retain the chosen finite overfield and actual splitting of the
supplied polynomials. This is not existence of an infinite p-special closure,
and does not assert that every small-degree polynomial over the new field is
linear. Any classwise Milnor application must first extract its finite
polynomial witnesses and supply a finite Galois splitting overfield.

Direct consumers: `MotivicTest/SylowFixedField.lean`, including root descent, the
prime-power degree, zero and constant polynomials, base-degree coprimality, and
the simultaneous finite-family endpoint. The test also inspects every source
and consumer declaration's checked proof body for nonstandard axioms.

## Coprime coefficient extensions and finite simultaneous splitting

`CoprimeIrreducibility.lean` has Mathlib-only imports. Its declarations in
`Polynomial` prove that a monic irreducible polynomial remains irreducible
under a finite coefficient extension of degree coprime to its natural degree.
For each actual irreducible factor, the root's original-base minimal polynomial
and finite tower formula imply divisibility of the factor degree by the
original degree. This requires neither perfectness nor separability.

`FiniteCoprimeSplitting.lean` combines the finite Sylow result with the actual
splitting field of a finite product. The base is explicitly perfect; each
supplied polynomial is nonzero and has degree below the prime. Perfectness
makes the finite splitting field separable and hence Galois even when the
product has repeated factors. The empty family has product one. The conclusion
is an actual finite intermediate field of degree prime to the chosen prime
which splits exactly the supplied family. It is not a global degree-gap result.

Direct consumers in `MotivicTest/FiniteCoprimeSplitting.lean` cover arbitrary finite
and purely inseparable coefficient extensions, linear and prime-degree
polynomials, empty families, repeated linear factors, characteristic two, and
characteristic zero. The Milnor-specific finite class application is in
`Motivic/KTheory/MilnorK/FiniteMixedGeneration.lean`.
