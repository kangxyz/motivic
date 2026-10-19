# Weight-two computations and comparisons

| Exact import | Interface |
| --- | --- |
| `Motivic.Cohomology.WeightTwo.MilnorNormComparison` | Original symbol/norm comparison; retain the leaf hypotheses |

`Motivic.Cohomology.WeightTwo` is the opt-in aggregate of the implemented
family, including the two endpoint computations. Its precise lower leaves
remain available.

This family retains actual weight-two cycles, symbols, field-change maps and
norm/corestriction comparisons. It consumes the
[current motivic model](../SuslinVoevodsky/README.md), actual geometric endpoint
constructions and independent Aglib's `MilnorK.K`, `MilnorK.K2.Group` and their
explicit symbol-preserving comparison.

Each leaf retains its own field, characteristic, finite-dimensional,
scalar-tower, valuation, normalization, support and derived-category hypotheses.
The optional family aggregate imports implemented leaves; importing it does
not strengthen their statements. General Milnor theory has one upstream
implementation. Geometric comparisons and transfer applications remain here.

`MotivicTest.WeightTwoMilnorNormComparison` is an existing consumer of the
original symbols and norm comparison. Preserve actual coefficient maps,
cycles, multiplicities and boundary relations. This family does not supply an
unqualified all-base or all-characteristic comparison, a general relative
Picard theorem, or a higher-Chow/motives/spectrum equivalence.
