# Polynomial normality, graph and diagonal regularity

These leaves extend the native `MvPolynomial`, `MvPolynomial.Graph` and
`MvPolynomial.Diagonal` namespaces. Their import closure contains only Mathlib,
Aglib and general candidates.

## Finite-variable integral closedness

`Motivic.Aglib.RingTheory.MvPolynomial.IsIntegrallyClosed` supplies
`MvPolynomial.isIntegrallyClosed_fin`: for every `n : ℕ`,
`MvPolynomial (Fin n) R` is integrally closed when the commutative ring `R`
is a domain and integrally closed. The coefficient universe is unrestricted;
no Noetherianity or characteristic premise is added.

The induction uses `MvPolynomial.isEmptyRingEquiv`, `MvPolynomial.finSuccEquiv`
and the univariate instance from its only import,
`Mathlib.RingTheory.Polynomial.IsIntegral`. Current direct consumers are
`Motivic.Aglib.RingTheory.Ideal.GoingDown.Polynomial` and
`Motivic.Aglib.RingTheory.Smooth.Normal`; the latter does not acquire integral
extension going down. `MotivicTest.GoingDownBaseChange` exercises these interfaces.

## Original coordinate equations and Koszul resolutions

| Exact import | Interface and boundary |
| --- | --- |
| `Motivic.Aglib.RingTheory.MvPolynomial.RegularSequence` | A duplicate-free finite list of variables is weakly regular over every commutative coefficient ring. |
| `Motivic.Aglib.RingTheory.MvPolynomial.Graph` | Actual equations `X i - C (c i)`, their evaluation kernel and quotient equivalence; duplicate-free lists are weakly regular, and regular when the coefficient ring is nontrivial. |
| `Motivic.Aglib.RingTheory.MvPolynomial.Diagonal` | Actual differences between the two variable copies, their evaluation kernel, quotient and translation equivalence, with the same list regularity conditions. |
| `Motivic.Aglib.RingTheory.MvPolynomial.DiagonalFlat` | Weak regularity on a supplied flat ambient module or under a supplied flat algebra base change. |
| `Motivic.Aglib.RingTheory.MvPolynomial.Diagonal.Koszul.Pair` | The genuine plane-diagonal projective resolution and categorical Tor calculation with arbitrary coefficient modules. |
| `Motivic.Aglib.RingTheory.MvPolynomial.Diagonal.Koszul.Finite` | The finite-dimensional diagonal resolution in every `n : ℕ`, actual Tor/Koszul comparison and vanishing above `n`. |

These equations and maps are reused by the general étale
[diagonal](../TensorProduct/EtaleDiagonal.lean) and
[graph](../TensorProduct/EtaleGraph.lean) interfaces. Ambient regularity or
flatness does not imply flatness or regularity of an arbitrary support module.
Intended upstream family: `Aglib.RingTheory.MvPolynomial`.
Follow the [candidate policy](../../README.md) and use the exact lower import.
