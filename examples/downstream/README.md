# Independent client

This separate Lake package requires `Motivic` by relative path and imports
`Motivic`. It checks the public correspondence category and the canonical
Milnor symbol quotient's degree-zero equivalence, without importing tests.

After resolving the root's committed dependencies and building its public entry,
run from the repository root:

```sh
python3 scripts/build.py Motivic
python3 scripts/build_client.py
```

The client helper inherits the root's locked dependencies without network setup,
shares only that checkout's package directory, and runs the guarded rehashed
build with private client outputs and receipts. It rejects foreign package links
and shared build-output links. CI selects this check for client changes and
changes reaching its public import. For distribution, replace the relative
requirement with this repository's URL and an exact reviewed commit.

Return to the [documentation routes](../../docs/README.md) for public imports and validation scope.
