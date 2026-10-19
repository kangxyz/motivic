# Finite morphisms and component images

`Components.lean` proves that a finite generalizing morphism sends every actual
generic-component closure onto a target irreducible component. Its finite-flat
specialization supplies the generalizing property from flatness. Neither scheme
needs to be irreducible, reduced, Noetherian, or nonempty. Finiteness alone does
not give the component assertion.

The native namespace is `AlgebraicGeometry.Scheme.Hom`. The leaf reuses the
existing generic-point generalization theorem, currently in the downstream
`Motivic.Aglib.AlgebraicGeometry.Morphisms.Generalizing.GenericPoints` module; extracting that
prerequisite is a separate ownership task. The current consumer is the full
finite-flat correspondence assembly, which retains all components and lengths.

## Whole finite charts, marked fibers and generic norms

| Exact import | Interface and retained boundary |
| --- | --- |
| `Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberChartNorm` | Canonical affine-chart comparison for the original whole generic fiber and scalar action. |
| `Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberLineRatio` | Ratio of the two original monic line-bundle maps on the finite Artinian generic fiber. |
| `Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberFunctionalNormProduct` | Native norm/product germ from the same functionals; only the target is integral. |
| `Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Marked.BaseChangeSquare` | Whole finite-fiber and marked squares constructed by actual pullback pasting. |
| `Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Marked.GraphChartFactors` | Actual marked/residual scheme maps from the original square and chart projection. |

Generic ratios use the entire finite generic fiber, including disconnected or
nonreduced sources, instead of an artificial source function field. Canonical
affine identifications preserve the original structural scalar maps. Each norm
interface retains its displayed target normality, finite/local-free, regularity
and genuine Cartesian base-change hypotheses; no unsupported freeness of a
residual component is inferred from freeness of the total chart.

Residual transport preserves the original residual open and its scheme map
into the full thickened boundary. Nilpotents and both injections are retained;
a range statement alone is not a boundary value or norm equation. For curve/frame and cycle applications, see the
[relative-curve interfaces](../../RelativeCurve/README.md) and
[cycle comparisons](../../Cycles/README.md).
