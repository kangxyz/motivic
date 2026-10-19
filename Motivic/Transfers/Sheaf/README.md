# Nisnevich sheaves with transfers

`Motivic.SheafWithTransfers` is the actual additive Nisnevich transfer-sheaf
category. Graph restriction is the canonical ordinary Nisnevich sheaf. The
usable sheafification coefficient universe is `u+1` over a field `k : Type u`.
Ordinary sheaves on the `Cor` topology are not indiscriminately identified with
the additive transfer-sheaf category.

| Exact import | Interface and boundary |
| --- | --- |
| `Motivic.Transfers.Sheaf.Basic` | The actual additive sheaf category and ordinary graph restriction |
| `Motivic.Transfers.Sheaf.Exactness` | Genuine sheaf exactness interfaces |
| `Motivic.Transfers.Sheaf.UnderlyingExactness` | Exactness of the actual ordinary graph restriction |
| `Motivic.Transfers.Sheaf.EnoughInjectives` | Injective infrastructure for the original transfer sheaves |

The [presheaf family](../Presheaf/README.md) supplies additive actions and
transfer-preserving sheafification, with a canonical comparison to ordinary
sheafification and identified units. Reflective sheaf cokernels are sheaf
colimits; section values need not be objectwise cokernels. Exactness alone does
not prove that underlying transfer-injectives are acyclic: use the actual
comparison proofs in [ordinary cohomology with transfers](../Cohomology/README.md).

Original germ envelopes and finite representatives remain actual objects and
maps. Their locality, lift-independence, exactness and acyclicity leaves retain
their own hypotheses. They do not construct a new replacement cohomology provider.
The direct endpoint consumer is `MotivicTest.OrdinaryCohomologyTransfers`;
[perfect-field strict invariance](../../Cohomology/A1/README.md) is a separate
consumer with coefficient HI and ordinary `HasExt.{u+1}`.
