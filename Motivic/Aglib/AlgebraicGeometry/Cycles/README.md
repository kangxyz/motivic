# AlgebraicGeometry / Cycles

Integral closed subschemes are the actual ideal sheaves whose subschemes are integral. IntegralCycle is their integer Finsupp group. Finite pushforward uses actual scheme-theoretic images and residue-field degrees, and intertwines the faithful generic-point dictionary. Fundamental cycles retain lengths of original, potentially nonreduced generic stalks.

Integral cycles and finite pushforward are over arbitrary schemes with the displayed finite-morphism premise. FundamentalCycle requires IsNoetherian; generic-stalk finiteness uses IsLocallyNoetherian; reducedness proves coefficient one. genericMultiplicity is a toNat construction even outside finite length, and is only identified with actual length under its finiteness hypotheses.

| Exact import |
| --- |
| `Motivic.Aglib.AlgebraicGeometry.Cycles.FundamentalCycle` |
| `Motivic.Aglib.AlgebraicGeometry.Cycles.IntegralCycle` |

Native interfaces:

- `AlgebraicGeometry.Scheme.IntegralClosedSubscheme`
- `AlgebraicGeometry.Scheme.IntegralCycle`
- `AlgebraicGeometry.Scheme.FiniteSupportCycle`
- `AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward`
- `AlgebraicGeometry.Scheme.fundamentalCycle`

Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic defines AlgebraicGeometry.AlgebraicCycle as locallyFinsupp, not this finite-support ideal-sheaf basis. Do not replace either object or assert a comparison without an explicit future mathematical interface. Existing Scheme.Hom.residueDegree is reused; infinite residue degree is natural-valued zero.

Host consumers include `Motivic.FiniteCorrespondence`, finite-flat correspondence cycles and fundamental-cycle pushforward.

Intended upstream family: `Aglib.AlgebraicGeometry.Cycles`. Use exact lower
imports; a current motivating consumer does not change the general hypotheses.
Follow the [candidate policy](../../README.md) and retain the actual maps and
universes when extending these interfaces.

## Original generic-ratio norm cycles

| Exact import | Interface and retained boundary |
| --- | --- |
| `Motivic.Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.GenericRatioNormCycle` | Original norm-cycle comparison using the whole generic fiber, target affine normality and a genuine local finite-free cover. |
| `Motivic.Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.RelativeAffineLineGraphNormCycle` | Original localized graph-target norm cycle with parameter and section choices made only after localization. |

Original zero schemes, scalar actions, multiplicities and residue degrees are
retained, including nonreduced support and image collisions. No artificial
function field of a disconnected finite source is introduced. General cycle
calculations stay here; actual signed correspondence and transfer applications
retain their host owners.
