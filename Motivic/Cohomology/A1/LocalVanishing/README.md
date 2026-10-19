# Original local-zero and generic-base vanishing

| Exact import | Interface and complete boundary |
| --- | --- |
| `Motivic.Cohomology.A1.GenericDetection` | Over infinite fields, original nonempty-open vanishing for HI presheaves with transfers on smooth integral affine schemes gives actual affine zero-neighborhoods covering every point. No sheaf premise; the conclusion is local zero. |
| `Motivic.Cohomology.A1.LocalVanishing.FiniteField.IntegralAffineLocalZero` | Constructed integral-affine local-zero neighborhoods over finite fields for original HI presheaves with transfers, with an arbitrary coefficient universe. No sheaf premise or supplied presentation family. |
| `Motivic.Cohomology.AffineLine.GenericBase` | Over any field and smooth domain base, classwise eventual higher vanishing for arbitrary ordinary coefficients and all-positive vanishing for HI transfer sheaves. Whole line, original restrictions, coefficient universe and ordinary `HasExt` retained; the base open is class-dependent. |

These are original-map local-zero suppliers, not replacements of the original
presheaf by an abstract isomorphic object. The finite and infinite suppliers
feed [perfect-field strict invariance](../README.md) together with the
[actual boundary Epi](../Boundary/README.md). A conditional helper retains its
explicit local-zero input even when another endpoint constructs a supplier.
Generic scheme neighborhoods have their
[candidate site owner](../../../Aglib/AlgebraicGeometry/Sites/README.md).
