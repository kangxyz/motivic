# Integral cycles, generic multiplicities and finite pushforward

For `X : Scheme.{u}`, `IntegralClosedSubscheme X` consists of ideal sheaves
whose actual closed subschemes are integral, and `IntegralCycle X` is their
integer-valued `Finsupp` group. Finite pushforward uses the scheme-theoretic
image and residue-field degree of each original component. Its point-cycle
comparison retains the faithful generic-point dictionary.

Integral cycles are defined on arbitrary schemes; `finitePushforward` requires
the actual morphism to be finite. `fundamentalCycle` requires `[IsNoetherian X]`
and retains lengths of the original, potentially nonreduced generic stalks.
Generic-stalk finiteness uses `[IsLocallyNoetherian X]`; reducedness gives
coefficient one. `genericMultiplicity` takes `toNat` even outside finite length,
so its identification with length retains the displayed finiteness hypotheses.

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

Mathlib's `AlgebraicGeometry.AlgebraicCycle`, in
`Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic`, uses `locallyFinsupp`.
A comparison with this finite-support ideal-sheaf basis requires its own map
and theorem. The existing `Scheme.Hom.residueDegree` is reused; an infinite
residue-field degree has natural-valued degree zero.

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
