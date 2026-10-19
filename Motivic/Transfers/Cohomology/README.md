# Ordinary Nisnevich cohomology with transfers

`Motivic.Transfers.Cohomology.Basic` constructs the canonical all-degree action
on the original ordinary Nisnevich cohomology groups. It works over any field,
for a Nisnevich sheaf with transfers and `n : ℕ`. Ordinary `HasExt` and the
coefficient universes remain explicit; the transfer-category `HasExt` instance
is constructed internally. Neither perfection nor coefficient HI is required.

| Exact import | Interface |
| --- | --- |
| `Motivic.Transfers.Cohomology.Basic` | `Motivic.SheafCohomology.withTransfers`, `withTransfersGraphIso`, `withTransfers_graph`, `withTransfersMap` |
| `Motivic.Transfers.Cohomology.Ordinary` | Original ordinary-cohomology transfer comparison |
| `Motivic.Transfers.Cohomology.Ext.Presheaf` | Transfer Ext presheaf on the actual category |
| `Motivic.Transfers.Cohomology.Ext.OrdinarySource` | Actual ordinary source used by the Ext comparison |
| `Motivic.Transfers.Cohomology.Ext.OrdinaryComparison` | Original ordinary/transfer Ext comparison and naturality |

The final group is literally ordinary cohomology. `withTransfers_graph` is the
original restriction, and `withTransfersMap` uses the original coefficient map.
The four host API names remain under `Motivic.SheafCohomology`; general ordinary
cohomology declarations have the native
`CategoryTheory.Sheaf.LargeCohomology` owner. See the
[general guide](../../Aglib/CategoryTheory/Sites/SheafCohomology/Large/README.md).

The construction consumes actual transfer-sheaf exactness and enough injectives,
underlying ordinary acyclicity, and the Ext comparison. Reflective sheaf
cokernels are genuine sheaf colimits. Exactness of graph restriction alone does
not establish acyclicity. Use the actual original-map comparison proofs.

`MotivicTest.OrdinaryCohomologyTransfers` consumes graph restrictions, signed
composition, literal group identity and standard-axiom dependencies.
[Perfect-field strict invariance](../../Cohomology/A1/README.md) is a separate
consumer; it retains ordinary `HasExt.{u+1}` and HI transfer-sheaf coefficients
in universe `u+1`. See [transfer sheaves](../Sheaf/README.md) for lower
infrastructure and [development](../../../docs/DEVELOPMENT.md) for validation.
