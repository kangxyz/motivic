# Finite correspondences and host geometry

This host owner contains actual signed finite correspondences and their
composition, graph, base-change, endpoint, moving and support constructions.
Use [the correspondence guide](Correspondences/README.md) and the small
`Motivic.Cor` public facade.

Reusable general geometry is maintained in
[Motivic/Aglib/AlgebraicGeometry](../Aglib/AlgebraicGeometry/README.md), grouped
by its actual schemes, morphisms, module sheaves, sites and cycles. General
curve, line-bundle, frame and pencil theorems remain candidates when their full
interfaces are general. Their motivic specializations consume those candidates.

[Transfer presheaves](../Transfers/Presheaf/README.md),
[transfer sheaves](../Transfers/Sheaf/README.md) and
[singular complexes](../Transfers/SingularComplex/README.md) have their own
host owners. The original ordinary-cohomology transfer action lives under
[Transfers/Cohomology](../Transfers/Cohomology/README.md).

Preserve actual incidence Tor coefficients, graph restrictions, divisor
schemes, boundary trivializations and original scalar maps. Finite-flat or
relative-Cartier correspondence producers do not close unrelated global
standard-triple, Picard or model-comparison obligations. See
[interfaces](../../docs/INTERFACES.md) for conditions and
[architecture](../../docs/ARCHITECTURE.md) for dependency direction.
