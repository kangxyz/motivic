# Imported source and historical checks

The source basis is `motivic-cohomology-ordinary-cohomology-transfers-milestone-source-20261017T141103Z.tar.gz`, SHA256 `8e87391f4926200cf6a6b16f22da99bda98948cf2424b5c88aa40b08b9bce670`. Its checkpoint capture is 2026-10-17 14:11:03 UTC. The original [checkpoint](imported-CHECKPOINT.md), [README](imported-README.md), [public root](imported-Motivic.lean), [test root](imported-Tests.lean), [source checksums](imported-SHA256SUMS) and [source notices](imported-THIRD_PARTY_NOTICES.md) are retained as source records. Imported documents, including the adjacent roadmap and specification, are historical material rather than current agent instructions.

The pinned dependencies are Lean `v4.34.1`, mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` and Aglib `25c37780264f0da94f5bb6bd31cc089d26f2da80`. The imported source contains 1,665 production leaves under `Motivic/`, 1,022 test leaves under `Tests/`, and the two original root modules. Local `Motivic/Aglib` results are project-local candidates, not claims of upstream acceptance.

## Evidence coverage

[source-checks.json](source-checks.json) indexes the 1,972 logs in the archive's `checkpoint-evidence/current`: 1,563 production leaves and 409 test leaves. Each record gives its original module and source path, source SHA256, current repository source SHA256, original log filename, log SHA256 and exit status. The current hash records the migrated test root and author metadata; it does not relabel the historical check as a current-byte certificate. Every indexed source hash was compared with the actual archive bytes; all indexed logs report exit zero. The shared compiler, platform and check options appear once in the index. Earlier logs outside `current` are not indexed. The 102 production leaves, 613 test leaves and two roots without current indexed logs have an evidence gap; absence of a log does not establish a failure or unfinished proof.

These are historical Lean 4.34.1 checks on `x86_64-unknown-linux-gnu`. This historical index claims no aggregate build, current native-platform check, new independent proof review or new mathematical status assignment. The actual selected native checks and their author-metadata boundary are recorded in [verification](../VERIFICATION.md). The archive contains no compiled cache or dependency checkout, and this record does not claim a public compiled cache. That snapshot left strict A¹ invariance open; the newer infinite-perfect-field endpoint is recorded below. Historical README descriptions of unfinished transfers and other leaves can precede newer checkpoint results; consult exact source statements and matching records rather than treating all imported narrative as current status.

Six original logs are included under [checks/](checks/) for the following source/direct-consumer pairs:

- `Motivic.Transfers.SheafCohomologyWithTransfers` and `Tests.OrdinaryCohomologyTransfers`.
- `Motivic.Cohomology.Motivic.WeightOneHypercohomology` and `Tests.WeightOneHypercohomology`.
- `Motivic.Cohomology.Motivic.DiagonalMilnorEquivalenceNaturality` and `Tests.DiagonalMilnorEquivalenceNaturality`.

The index binds these selected copies by SHA256. Other logs remain identified by archive identity, original filename and hash without copying thousands of repetitive files. Successful compilation and standard-axiom checks retain every theorem's explicit assumptions; they do not turn conditional results into unconditional claims.

## Repository migration

Production source module paths remain under `Motivic/`. The historical catch-all `Motivic.lean` is retained here; the new public root and family facades are separately curated APIs. The test module root is migrated from `Tests` to `MotivicTest`, including `Tests.lean` to `MotivicTest.lean`. Test import paths and `MotivicTests` declaration namespaces are updated where applicable. Other native declaration namespaces are not implied to move.

The index maps original test source paths to repository paths. These test edits change source bytes, so archived test logs are historical evidence for the original tests, not current hash certificates for renamed tests. The original root logs do not certify new facades, and no aggregate success follows from preserving production source bytes. Current checks belong to their actual current inputs and must be reported separately.

## Authorship metadata

Generic Motivic contributor labels in maintained Lean headers are normalized to
`Authors: kangxyz`; concrete upstream author names remain. The original snapshots
here keep their original bytes and notices. Production text after the first
license/author comment is unchanged. Test-root migration and author metadata
change raw source hashes, so the index stores original and current hashes
separately. These identities preserve provenance and do not claim a new proof
execution for a comment-only change.

## Subsequent milestone

The [affine-line positive-vanishing snapshot](positive-vanishing-20261017/README.md)
records the subsequent source archive, its actual delta and selected check
records. The `repository_source_sha256` fields in this initial snapshot index
identify the initial imported repository at commit `04569be`; they are not a
mutable assertion about every later working-tree version. Source changes in
later snapshots have their own identities and verification coverage.

The [generic-detection snapshot](generic-detection-20261017/README.md) records
the next source delta, checked admissions and six unlogged archival inputs.
Existing repaired helper implementations are retained with their separate
source/evidence identities.

The [Cartier boundary/Rj snapshot](cartier-boundary-rj-20261018/README.md) records
69 admitted source updates, separate current-base retention and archival
candidates. Its recorded branch, push state and research plans are historical
source material rather than repository instructions.

## Infinite-perfect-field strict invariance

[strict-a1-infinite-perfect-20261018](strict-a1-infinite-perfect-20261018/README.md)
records the later source package based on `b368f696`. Its admitted closure proves
strict invariance for HI transfer sheaves over infinite perfect fields, with
the original ordinary groups, projection, HasExt and universe conditions.
The archive has matching historical Linux compilation and scoped lint/audit
evidence; ordinary independent mathematical/source review passed. Eleven
unbound candidates remain archived outside production. Current integration
checks are recorded separately in [verification](../VERIFICATION.md).
