# Test and trust consumers

The Lake library and module root are `MotivicTest`. The focused root selects
`PublicAPI` and `OrdinaryCohomologyTransfers`; further imported consumers can
be built by exact module name.

`PublicAPI` imports only `Motivic` and checks category instances and the
literal original ordinary cohomology groups. `OrdinaryCohomologyTransfers`
checks graph restrictions, signed composition, original group identity and
transitive standard-axiom dependencies.

The source archive used the generic `Tests` root and several declaration
namespaces. Module imports and the `Tests`/`MotivicTests` test namespaces were
renamed mechanically. Native object extensions remain under their original
mathematical namespaces. Original Linux test hashes therefore describe the
imported bytes, not the renamed current test files; see
[provenance](../doc/provenance/README.md).

Tests and independent clients never define prerequisites for production.
A positive fixture or axiom audit cannot discharge a mathematical premise.
