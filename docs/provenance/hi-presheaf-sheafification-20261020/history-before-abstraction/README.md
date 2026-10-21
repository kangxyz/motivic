# History adapters before abstraction

These recovery copies preserve the concrete adapters before the abstract-data refactor.
They are outside the maintained Lean module tree and are not imported.
The snapshot has Git HEAD `57e94dc5db72b38129032ed2d39a2fd5117e9f9e` plus the current CI repairs.
Its native incremental library build and package tests passed (8006 jobs); both shared declaration-lint drivers passed.
The source-script checks still required missing pinned tool dependencies.

The downstream source search found no direct imports or qualified API references
to these history modules; their active in-library consumers are migrated with the refactor.

| Original source | SHA-256 |
| --- | --- |
| `Motivic/Transfers/Presheaf/Actions/Norm/NativeRefinement/OriginalHistory.lean` | `5db87a5fb63a608d8f21bfe30853ca105e0978be227ae0a9d161d2acfbb12cf1` |
| `Motivic/Transfers/Presheaf/Actions/Norm/NativeRefinement/OriginalHistoryLine.lean` | `c30758a6d9e40af4a95e9f8a401f3096f5cbc09d3d071d747608b5d4bd670632` |
| `Motivic/Transfers/Presheaf/Actions/Norm/NativeRefinement/OriginalHistoryRestrictions.lean` | `d43f51de8625bb141ce87a22b3beadca6631c3dc63841f832ecfc82a57296d06` |
| `Motivic/Transfers/Presheaf/Actions/Pencils/OriginalHistoryMiddleRelations.lean` | `d32d3dcb1e2215893c242e23abfdfa518f379b43c4b12dbd0ce6fe9b7033e326` |
| `Motivic/Cohomology/A1/Sheafification/OriginalHistoryLifting.lean` | `fb5177902ca912a352a16c71442bb6ecc118cc0ea82e40a040693efb17564797` |
| `Motivic/Cohomology/A1/Sheafification/WholeCylinderLifting.lean` | `69d767ff2b60ce58fd2cf04f188e4c1c7da81212f3794a77582ceddadda2c5e1` |
