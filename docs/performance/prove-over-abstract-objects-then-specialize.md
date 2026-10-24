> Preserved original record. [Original source](https://github.com/kangxyz/motivic/blob/be8e17f5286874bd44942f796b96860b4b924993/docs/PERFORMANCE.md#prove-over-abstract-objects-then-specialize) · [Context](original-context.md) · [Case index](README.md) · [Previous record](observed-module-costs.md) · [Next record](reuse-the-build-environment.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Prove over abstract objects, then specialize

The expensive concrete terms combine nested coefficient restrictions, global
section rings, polynomial lines, smooth-site structures and their instance
proofs. Passing those terms into every inference and equality comparison caused
large repeated conversion obligations. The successful encoding changes suggest
conversion at these boundaries was significant; these module measurements alone
do not separate elaboration, instance search and kernel checking costs.

[NativeCover](../../Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/AffineLine/NativeCover.lean)
proves affineness, étaleness and restriction squares over `R : CommRingCat` and
literal scheme maps. `affineEtaleOverArrow` receives the actual target site
object. This avoids reconstructing an extensionally identical target with
different structure or instance expressions. The application modules then
specialize those helpers once. The underlying-arrow equalities remain `rfl`.
[OriginalNativeCover](../../Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/Nisnevich/OriginalNativeCover.lean)
proves field lifting for abstract actual arrows with explicit underlying-map
equalities before receiving the original representatives.

[LocalizationHistory](../../Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/AffineLine/LocalizationHistory.lean)
proves the native line and source endpoint equalities over the existing abstract
localization witnesses. The application-level
[OriginalHistory](../../Motivic/Transfers/Presheaf/Actions/Norm/NativeRefinement/OriginalHistory.lean)
packages geometry, localization choices and witnesses in `OriginalHistoryContext`.
Line and restriction adapters consume that one context. The generic history's
`SourceSections` and `TargetSections` name the unchanged rich supplier predicates.
The lifting producer converts those suppliers to witnesses over an abstract
`OriginalHistoryData`, then constructs its context. `WholeCylinderLifting` passes
its original suppliers to that producer without unpacking the witness records
in the concrete geometric context. The raw
action-difference proof is checked over `NativeOriginalMiddleInput` with an
explicit source equality; its history specialization discharges that equality
by `rfl`. The shared context avoids repeating long parameter lists and building
the same concrete native input in each wrapper.

The original maps, chosen witnesses, E3 correction sign, coefficient universe
`u + 1` and public theorem hypotheses are retained. General localization APIs
remain maintained; superseded concrete wrappers are preserved as
[non-imported recovery copies](../provenance/hi-presheaf-sheafification-20261020/history-before-abstraction/README.md).
Abstraction is useful when it reduces repeated conversion; the intermediate
constructor regression shows that packaging alone does not guarantee a faster
consumer.

The targeted diagnostic of the 300-second version reported an elaboration
interval of 314.34 seconds before a `whnf` timeout at 200000 heartbeats. Its
partial counters included 555 unfolds of `OriginalHistorySeedData.toSeed`,
8291 of `toOriginalRepresentativeGeometry` and 6974 of
`toOriginalHistorySeedData`, alongside repeated scheme and structure-sheaf
projections. This suggested moving the complete supplier-to-witness conversion
across the abstraction boundary. The diagnostic did not complete a kernel check
and supplies no successful build or per-constant timing. Its additional
diagnostic output and single-file setup make its 563.50-second total unsuitable
as an ordinary module benchmark. The retained repair passed a normal native
build with the unchanged 200000-heartbeat budget.

