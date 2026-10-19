# General scheme sites and Nisnevich maps

This family uses actual scheme categories, cover families, neighborhoods and
residue-field maps. Topology and coefficient conditions remain on each lower
interface. The native declaration namespaces differ from their import paths.

| Exact import | Actual object and scope |
| --- | --- |
| `Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Basic` | `AlgebraicGeometry.Scheme.SmoothSite`: smooth, separated, quasi-compact maps over a base |
| `Motivic.Aglib.AlgebraicGeometry.Sites.Nisnevich.Basic` | General Nisnevich cover conditions on the original schemes and residue maps |
| `Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Nisnevich` | `Scheme.EtaleSeparatedFiniteType` and its Nisnevich topology |
| `Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.CohomologyComparison` | Original comparison maps with their explicit sheaf, universe and Ext conditions |

See the [smooth-site guide](Smooth/README.md) and
[étale separated finite-type guide](Etale/SeparatedFiniteType/README.md).
The latter objects are étale, separated and quasi-compact; they are not required
to be finite. They differ from Aglib's `Scheme.FiniteEtale`, and their topology
is Nisnevich. Smooth implies locally finite presentation; quasi-compactness
supplies the finite-type condition in the smooth object selection.

Generic original germs and inverse-image comparisons use the actual neighborhood
colimits. Covers use their actual pullbacks; the smooth category is not asserted
to have arbitrary pullbacks. Noetherian, affine, coefficient-universe and
injective/derived conditions remain where stated. An arbitrary extension field
is not silently an object of a finite-type site.

Host consumers include `Motivic.Cor`, graph restriction of transfer sheaves,
boundary cohomology and the current motivic model. Transfer actions and HI
specializations stay outside this candidate family. Use the
[general sheaf-cohomology guide](../../CategoryTheory/Sites/SheafCohomology/Large/README.md)
for the actual large-universe Ext construction and the
[hypercohomology guide](../../CategoryTheory/Sites/Hypercohomology/README.md)
for unbounded derived Hom.
