# Retained local-length adapters

General ring theory is maintained in
[Motivic/Aglib/RingTheory](../Aglib/RingTheory/README.md), with a general import
closure and native namespaces. This host directory retains six existing
local-length compatibility adapters, without a second implementation.

| Exact import |
| --- |
| `Motivic.RingTheory.LocalLength.PrincipalEuler` |
| `Motivic.RingTheory.LocalLength.PrincipalEulerSupport` |
| `Motivic.RingTheory.LocalLength.PrincipalEulerAdditivity` |
| `Motivic.RingTheory.LocalLength.PrimeFiltration` |
| `Motivic.RingTheory.LocalLength.PrimeFiltrationMultiplicity` |
| `Motivic.RingTheory.LocalLength.PrincipalEulerFiltration` |

New implementation work uses the canonical lower Aglib/candidate source.
Preserve original scalar actions, length values and finiteness hypotheses;
source relocation does not strengthen a length identity. Actual correspondence
and geometric multiplicity consumers retain their own conditions.
