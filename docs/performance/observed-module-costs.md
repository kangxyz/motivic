> Preserved original record. [Original source](https://github.com/kangxyz/motivic/blob/be8e17f5286874bd44942f796b96860b4b924993/docs/PERFORMANCE.md#observed-module-costs) · [Context](original-context.md) · [Case index](README.md) · [Previous record](copyright-headers-and-cached-command-lint.md) · [Next record](prove-over-abstract-objects-then-specialize.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Observed module costs

Module names in the first four rows have prefix
`Motivic.Transfers.Presheaf.Actions.Norm.NativeRefinement`.
The last two are in `Motivic.Cohomology.A1.Sheafification`.

| Module | Before, seconds | After, seconds | Interpretation |
| --- | ---: | ---: | --- |
| `NativeOriginalRefinedSource` | 1845 | 96–97 | Native ring and scheme helpers before site specialization |
| `NativeOriginalRefinedPuncture` | 4325 | 555 | Shared restricted maps and an arrow over the actual target object |
| `OriginalHistoryLine` | 643 | 51 | Generic endpoint equalities and one abstract history context |
| `OriginalHistoryRestrictions` | 385 | 5.8 | Shared context instead of repeated concrete history reconstruction |
| `OriginalHistoryLifting` | 42 | 36 | Supplier conversion is checked over abstract history data |
| `WholeCylinderLifting` | 135 | 141 | Concrete producer passes the original rich suppliers directly |

The extracted `NativeOriginalRefinedCover` compiled in 67 seconds; no matching
successful baseline measurement is recorded. `OriginalHistoryMiddleRelations`
compiled in 4.6 seconds in the final affected build after its proof was moved
to the abstract native input.
Module times must not be summed into a whole-build speedup: dependency jobs can
overlap, and extraction moves work into new modules. The final constructor is
close to its original 135-second cost; no improvement over that baseline is
claimed. Its first context-based version had regressed to 300 seconds. Moving
the complete supplier conversion to the abstract lifting producer reduced that
observation to 141 seconds. The first context version reported 109 seconds for
Line, 8.5 for Restrictions and 31 for HistoryLifting; the table records the final
affected build, with its changed dependencies and allocation of work.

Two earlier constructor variants did not resolve that regression. Explicitly
constructing the inherited parent records took 294 seconds, close to the
300-second observation. Selecting the two nonempty section witnesses in a
separate abstract context constructor took 319 seconds. Neither variant is
retained. These observations do not support claiming that either rearrangement
reduced the remaining cost. The retained repair moves supplier conversion into
the abstract producer rather than just rearranging the final record literal.

