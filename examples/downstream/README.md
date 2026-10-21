# Independent client

This separate Lake package requires `Motivic` by relative path and imports
`Motivic`. It checks the public correspondence category and the canonical
Milnor symbol quotient's degree-zero equivalence, without importing tests.

The common CI configuration declares this independent package. From a prepared
repository root, select its public library interface through the same CLI:

```sh
python3 -m lean_ci check --config .github/lean-ci.toml --root . \
  --target Motivic --progress /absolute/scratch/motivic-check-progress
```

Common native preparation inherits the root's locked dependencies, shares only
this checkout's package directory, and keeps private client outputs. It rejects
foreign package links and shared build-output links. The incremental selector
includes the client for client-input changes or changes reaching its public
import. For distribution, replace the relative requirement with the repository
URL and an exact reviewed commit.

Return to the [documentation routes](../../docs/README.md) for public imports
and the [script guide](../../scripts/README.md#common-ci) for tooling setup.
