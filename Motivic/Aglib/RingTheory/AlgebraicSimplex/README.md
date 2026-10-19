# RingTheory / AlgebraicSimplex

The actual polynomial quotient by sum(coordinates)-1, its universal property, simplicial ring maps, polynomial coordinates and unit calculations. No scheme is defined in the coordinate-ring trio.

Original commutative-ring, variable-universe and reducedness conditions of individual unit results remain unchanged. Scheme realizations live in their geometric source owner and extend the same AlgebraicSimplex namespace.

| Exact import |
| --- |
| `Motivic.Aglib.RingTheory.AlgebraicSimplex.Basic` |
| `Motivic.Aglib.RingTheory.AlgebraicSimplex.Polynomial` |
| `Motivic.Aglib.RingTheory.AlgebraicSimplex.Units` |

Native interfaces:

- `AlgebraicSimplex.CoordinateRing`
- `AlgebraicSimplex.pullback`
- `AlgebraicSimplex.simplicialRing`
- `AlgebraicSimplex.mapCoefficients`

The scheme realization and singular parameter complexes consume the same coordinate-ring object.

Intended upstream family: `Aglib.RingTheory.AlgebraicSimplex`. Use exact lower
imports; a current motivating consumer does not change the general hypotheses.
Follow the [candidate policy](../../README.md) and retain the actual maps and
universes when extending these interfaces.
