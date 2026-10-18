# Milnor interfaces and motivic applications

General Milnor K-theory is maintained in the independent
[Aglib repository](https://github.com/kangxyz/aglib), under
`Aglib.KTheory.MilnorK`. The canonical group is `MilnorK.K F n`; its lower-degree
tensor presentations live under `MilnorK.K2` and `MilnorK.K3` and are compared
by `twoEquiv` and `threeEquiv`. No separate top-level MilnorK2/MilnorK3 theory
is introduced.

The old `Motivic.KTheory.MilnorK*` paths are import adapters to Aglib.
New code should import focused Aglib leaves. The core facade is
`Aglib.KTheory.MilnorK`; characteristic-zero finite-extension norm transitivity
is available through `Aglib.KTheory.MilnorK.Norms`. All original characteristic,
valuation, normalization, universe and scalar-tower hypotheses are retained.

`AffineEndpointGeometry` and `NormalizedAffineEndpointNorm` remain here because
they compare against Motivic's original geometric endpoint and cycle objects.
The diagonal and weight-two cohomology comparisons remain in the motivic
cohomology family. Production Aglib code has no dependency on Motivic.

Source history remains in [provenance](../../../doc/provenance/README.md).
The copied K₂ source exceptions retain their original notices in Aglib;
the local compatibility leaves contain no copied mathematical implementation.
