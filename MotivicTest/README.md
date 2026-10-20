# Test and trust consumers

The Lake library and module root are `MotivicTest`. The focused root selects
`PublicAPI` and `OrdinaryCohomologyTransfers`; further imported consumers can
be built by exact module name.

`PublicAPI` imports only `Motivic` and checks category instances and the
literal original ordinary cohomology groups. `OrdinaryCohomologyTransfers`
checks graph restrictions, signed composition, original group identity and
transitive standard-axiom dependencies.

The optional `MotivicTest.HIPresheafSheafificationReduction` consumer retains
the actual sheafification and ordinary cohomology projections: sheafification
HI starts over a field at coefficient universe `u + 1`, while strict invariance
adds perfectness and ordinary `HasExt.{u + 1}`. It also keeps conditional lifting
interfaces selectable. It is not imported by the focused test root. The
[sheafification guide](../Motivic/Cohomology/A1/Sheafification/README.md) owns the
statements; [verification](../docs/VERIFICATION.md) records their validation
scope without treating the presence of a test as a completed check.

The source archive used the generic `Tests` root and several declaration
namespaces. Module imports and the `Tests`/`MotivicTests` test namespaces were
renamed mechanically. Native object extensions remain under their original
mathematical namespaces. Original Linux test hashes therefore describe the
imported bytes, not the renamed current test files; see
[provenance](../docs/provenance/README.md).

Tests and independent clients never define prerequisites for production.
A positive fixture or axiom audit cannot discharge a mathematical premise.

Return to the [documentation routes](../docs/README.md) for public imports and validation scope.
