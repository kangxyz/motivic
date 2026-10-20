# General finite-extension candidates

This occupied family extends actual field extensions and polynomial witnesses.
Use the exact lower import for its displayed field, degree, coprimality and
avoidance hypotheses. These are general interfaces; motivic specialization
stays outside the candidate closure.

| Exact import | Interface and boundary |
| --- | --- |
| `Motivic.Aglib.FieldTheory.FiniteExtension.Avoidance.Polynomial` | A nonzero polynomial in finitely many variables has a nonzero value in a finite field whose cardinality exceeds its total degree. Over a finite ground field, every sufficiently large positive extension degree works. |
| `Motivic.Aglib.FieldTheory.FiniteExtension.Avoidance.ResiduePolynomial` | A parameter makes the original residue polynomial a unit on the entire tensor fiber; a finite family uses one common parameter and the product of its norm polynomials. |
| `Motivic.Aglib.FieldTheory.FiniteExtension.Avoidance.WholeFiber` | For a finite free domain over the original polynomial ring, nonzero determinant norm gives a unit on the whole evaluation fiber, including all branches and nilpotents. |
| `Motivic.Aglib.FieldTheory.FiniteExtension.CoprimeTensorField` | `Algebra.TensorProduct.isField_of_coprime_finrank` makes the entire tensor algebra a field under the displayed coprimality condition; the canonical finite-field extension has its own specialization. |
| `Motivic.Aglib.FieldTheory.FiniteExtension.PrimeDegrees` | `Nat.exists_two_large_prime_degrees_coprime` supplies two distinct primes above a bound, coprime to each other and a prescribed nonzero natural degree; no field object is needed. |

The avoidance leaves use native `MvPolynomial` and `Algebra` namespaces, with
explicit independent field, coefficient-algebra and variable universes. Finite
residue extensions and finite parameter families remain hypotheses of their
respective interfaces. These leaves do not construct a geometric parameter
algebra or its finite free presentation.

Already accepted Sylow fixed-field, rational-function and Milnor interfaces use
pinned Aglib directly. A statement for an explicitly supplied finite polynomial
family is not a global p-special closure or a degree-gap assertion for every
polynomial over an extension. Current consumers are general scalar-extension
and geometric parameter constructions. See the [candidate policy](../README.md).
