# Lean performance findings

This guide keeps the key local methods and repair process. The complete
[case folder](performance/README.md) preserves original measurements, failed
variants and the source/run table. Common methods are maintained in
[Aglib's synthesis](https://github.com/kangxyz/aglib/blob/main/docs/PERFORMANCE.md).

## Key methods and conditions

**Prove geometry over actual abstract arrows, then specialize once.** Keep the
native target site object, ring/scheme maps and their literal comparison equations
in generic cover proofs. This avoids reconstructing equivalent targets with
different structures. The actual target object and original underlying-map
equations are part of the retained interface.
[Full cover/history cases](performance/prove-over-abstract-objects-then-specialize.md).

**Move complete supplier conversion across the boundary.** A context can share
geometry, localization choices and rich suppliers, but the concrete consumer
may still pay for unpacking and rebuilding witnesses. Convert the complete
supplier-to-witness data inside the abstract lifting producer. The concrete
caller passes its unchanged rich suppliers to that producer, which performs the
conversion before constructing the context. Keep original maps, chosen witnesses,
E3 sign, coefficient universe `u + 1` and public hypotheses.

More packaging alone is insufficient. The first history context and two
constructor variants regressed the recorded cost; the retained 141-second
observation does not improve the original 135-second one.
[All variants and module observations](performance/observed-module-costs.md).

**Separate compile-cache reuse from check coverage.** Cached outputs provide no
fresh execution of a command linter. The copyright repair covered its named
header predicate, not every checker or mathematical claim. Batch a needed source
repair while preserving compatible artifacts and use the current native check
entry for actual coverage.
[Complete header case](performance/copyright-headers-and-cached-command-lint.md).

**Reuse matching checker setup.** A same-module `[init]` interpretation failure
is a checker-launch failure, not a source-style finding. Reuse the compatible
compiled driver with matching Lean, dependency and source identity. Recover a
missing tool dependency rather than rebuilding unrelated mathematics.
[Complete build/checker case](performance/reuse-the-build-environment.md).

## Repair workflow

1. Locate the phase using existing feedback. Read the matching method/case and
   its original dependency/resource conditions before further experiments or
   budget changes.
2. Keep the actual maps, target objects, coefficient structures and witness
   equations. Choose a bounded representation repair; compare its concrete
   specialization with the interface the real consumer needs.
3. Build affected leaves and necessary in-package consumers incrementally.
   Preserve compatible outputs and successful checks; changing a wrapper or
   starting a new run does not itself justify whole-library recompilation.
4. If the cases do not apply, use Aglib's
   [upstream reference search](https://github.com/kangxyz/aglib/blob/main/docs/PERFORMANCE.md#search-upstream-references).
   Profiling, probes and matched timing comparisons are explicitly requested
   investigations, with the original source and output conditions retained.
5. When a validated repair adds new reusable knowledge, preserve a complete
   case or update its existing file, then refine the applicable method here
   while keeping the raw case and its index.

Use [development](DEVELOPMENT.md#source-and-contribution-conventions) for current
source/budget policy and [the toolkit guide](../scripts/README.md) for actual
commands. Historical checker sequences in the records do not add current stages.

## Interpret and preserve evidence

Module-job durations can overlap, extraction can move work and cached jobs have
no new timing. The failed diagnostic's total is not an ordinary module benchmark.
Keep the distinctions between repaired module, failed enclosing graph, final
integration and mathematical correspondence; see the complete
[source/run record](performance/source-and-log-evidence.md).

Keep the actionable methods/process in this guide and all original case detail
under `docs/performance/`. Preserve both when adding knowledge: neither
a summary nor a Git link replaces saved case text, and case preservation does
not remove the synthesis here. Another run/pass or unchanged use of a known
method needs no new entry; existing records stay complete. Documentation creates
no new build, benchmark or acceptance cycle.
