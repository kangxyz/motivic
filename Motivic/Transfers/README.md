# Ordinary cohomology with transfers

[Motivic.Transfers](../Transfers.lean) exports
[SheafCohomologyWithTransfers](SheafCohomologyWithTransfers.lean), the canonical
all-degree endpoint on the original ordinary Nisnevich cohomology groups.
It works over any field, for a Nisnevich sheaf with transfers and `n : ℕ`.
The original ordinary `HasExt` and coefficient universes remain explicit;
the transfer-category `HasExt` instance is constructed internally.

The intermediate interfaces are sheaf exactness and exact graph restriction,
enough injectives, ordinary acyclicity of transfer injectives, the actual Ext
comparison and its graph/coefficient naturality. Use their exact leaves when
working on one step. The final group is literally ordinary cohomology;
`withTransfers_graph` is the original restriction and `withTransfersMap`
uses the original coefficient map.

The direct consumer is
[MotivicTest.OrdinaryCohomologyTransfers](../../MotivicTest/OrdinaryCohomologyTransfers.lean).
The imported endpoint and all 560 local modules in its closure have exact
hash-matched successful Linux checks. This historical coverage does not assert
a new aggregate native build or supply independent mathematical review.

Strict A1 invariance remains open. Neither homotopy invariance nor perfectness
is a premise of the endpoint. Ordinary sheaves on the `Cor` topology must not
be identified indiscriminately with the additive transfer-sheaf category.
