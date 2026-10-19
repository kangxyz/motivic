# General Milnor K-theory upstream integration

The implementation owner is the independent `kangxyz/aglib` repository.
Its [source correspondence](https://github.com/kangxyz/aglib/blob/b11b71d11bf03cf231f0e06b947a7b63d4344a9e/doc/migration/motivic-milnor-k.json)
records 273 moved implementation modules, one generic polynomial cut and 170
moved tests against Motivic source revision `b368f696`.

The canonical group is `MilnorK.K F n`; the tensor presentations are
`MilnorK.K2.Group F` and `MilnorK.K3.Group F`. Motivic retains its actual endpoint
geometry and comparison applications. Import adapters preserve old module
paths without retaining parallel implementations. Source licenses and complete
hypotheses remain explicit.

[CHECKS.json](CHECKS.json) separates current native producer/consumer identities,
controlled compatible reuse and hosted validation. No whole-library replay or
new mathematical proof status is claimed by the relocation.
