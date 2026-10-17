# Motivic

A Lean library for motivic cohomology, finite correspondences, Nisnevich
sheaves with transfers, and Milnor K-theory. The library grows from concrete
objects and maps: signed correspondence cycles, the Suslin complex of the
reduced torus, ordinary Nisnevich hypercohomology, and actual Milnor symbol
quotients.

```lean
import Motivic
```

The default entry selects the core interfaces. Prefer a family or exact leaf
when working on one subject:

| Import | Interface |
| --- | --- |
| `Motivic.Cor` | Finite correspondences, graph functor, transfer presheaves and Nisnevich sheafification |
| `Motivic.Transfers` | Signed transfers on the original ordinary Nisnevich cohomology in every nonnegative degree |
| `Motivic.Cohomology` | Ordinary/relative cohomology and motivic complexes with integral/finite coefficients |
| `Motivic.Cohomology.Motivic` | Canonical motivic complexes and hypercohomology |
| `Motivic.Cohomology.AffineLine` | Optional ordinary higher vanishing and positive-degree vanishing for HI sheaves with transfers |
| `Motivic.KTheory.MilnorK` | Milnor groups, products, field maps and residues |
| `Motivic.KTheory.MilnorK.Norms` | Optional characteristic-zero finite-extension norm and tower laws |
| `Motivic.Cohomology.Motivic.Diagonal` | Optional characteristic-zero diagonal comparison |
| `Motivic.Cohomology.Motivic.WeightOne` | Optional weight-one ordinary-sheaf and hypercohomology comparisons |

`Motivic` identifies the package and import root. Declarations retain their
mathematical owners: for example `Motivic.Cor`, `Motivic.SheafWithTransfers`,
`Motivic.SheafCohomology.withTransfers`, and native `AlgebraicGeometry` and
`CategoryTheory` namespaces. The test package uses `MotivicTest`.

## Setup and focused checks

Lean is pinned to **4.34.1**, Mathlib to
`d13f23b723b8a846827a245b89c10fc7d3f11612`, and Aglib to
`25c37780264f0da94f5bb6bd31cc089d26f2da80`. Keep the committed manifest.

```sh
lake resolve-deps
python3 scripts/cache.py --guarded --resolve-deps Motivic.KTheory.MilnorK.Basic
python3 scripts/build.py Motivic.KTheory.MilnorK.Basic
```

All normal workflows use incremental checks. Develop with selected-module
compilation and its diagnostics; run independent lint and affected `MotivicTest`,
client and tooling tests only in the task's final validation before delivery.
Reuse compatible evidence and rerun only failed or newly affected checks after
repairs. Merge, publication and intermediate handbacks do not trigger them.

See [development](doc/DEVELOPMENT.md#verification-by-scope) for check categories,
timing, dependency caches, selected consumer
checks, CI and the shared native-cache publication protocol. The [source guide](Motivic/README.md) locates the current owners;
[architecture](doc/ARCHITECTURE.md), [naming](doc/NAMING.md), and
[interfaces](doc/INTERFACES.md) explain extension boundaries.

## Mathematical and verification scope

The imported 17 October 2026 milestone constructs finite transfers on the
**original ordinary** Nisnevich cohomology for any field, a Nisnevich sheaf
with transfers, and every nonnegative degree. The final endpoint exposes only
the original ordinary `HasExt` bookkeeping; graph action agrees with original
restriction, and original coefficient maps respect transfers. It does not
assume homotopy invariance.

The 17 October 2026 affine-line milestone proves vanishing of original ordinary
`H^(n+2)(A1_k,F)` for arbitrary ordinary abelian Nisnevich coefficients on the
smooth site over any field, and `H^(n+1)(A1_k,F)` for homotopy-invariant
Nisnevich sheaves with transfers. The original ordinary `HasExt` and coefficient
universes remain explicit. Use `Motivic.Cohomology.AffineLine` for this optional
computation. Its [source/evidence record](doc/provenance/positive-vanishing-20261017/README.md)
records the exact scope and preserved boundaries.

Strict A1 invariance remains open. The diagonal Milnor comparison retains its
characteristic-zero and derived-category hypotheses. The weight-one comparison
uses ordinary Nisnevich sheaves. General higher-Chow, motives and spectrum
comparisons are future work with separate proof obligations.

The initial snapshot and the subsequent affine-line milestone sources are
retained, including their exact input and evidence records. A focused umbrella
is a usable import selection, not a claim that every retained source or every open programme is complete. Original
hash-matched Linux check records and exact migration details are in
[provenance](doc/provenance/README.md). They are historical evidence, not a new
aggregate build or independent proof review. See [verification](doc/VERIFICATION.md)
for this repository's actual checks.

## License and provenance

Project-authored code uses `Authors: kangxyz`; concrete upstream authors remain
credited. The Apache-2.0 text is retained in [LICENSE](LICENSE). The copied R5 Milnor K2
implementations retain their original license exceptions; see
[third-party notices](THIRD_PARTY_NOTICES.md). The repository owner explicitly
authorized public publication of the supplied code on 17 October 2026. This
authorization does not relabel those files as Apache-2.0.
