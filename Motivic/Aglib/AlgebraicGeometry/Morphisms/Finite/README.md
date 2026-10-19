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

## Functional norm products on the original good open

The native namespace `AlgebraicGeometry.Scheme` supplies
[FunctionalProduct/UnitDomain](Norm/FunctionalProduct/UnitDomain.lean).
For a finite `f : C ⟶ T`, source line-bundle functionals `n,d` and target
functionals `a,c`, `functionalNormProductUnitDomain` is the intersection of
the two target unit opens with `f.finiteDescentOpen` of the intersection of
the two source unit opens. Thus every point of the entire finite inverse
image lies in both source unit loci. `functionalNormProductBoundaryFactor`
factors the caller's original boundary morphism through this exact open,
using the displayed target invertibility and whole-inverse-image containment.
This factorization alone asserts no value-one equation.

When the numerator and denominator on each scheme have the same line bundle,
[FunctionalProduct/Unit](Norm/FunctionalProduct/Unit.lean) constructs a regular
unit with generic germ `(a/c) N_f(n/d)`.
`exists_functionalNormProductUnit_of_free_charts` requires integral `T`,
monicity of all four original functionals, nonemptiness of the good open,
and a genuine Cartesian presentation from a finite map with a covering family
of free affine charts. `functionalNormProductUnit_restrict` identifies the
section on every nonempty free affine subchart with the literal quotient/norm
product there. [UnitDomainGeneric](Norm/FunctionalProduct/UnitDomainGeneric.lean)
derives nonemptiness from those regularity and integral-target hypotheses.
These statements impose no integral-source hypothesis and supply no boundary
normalization until the separate boundary calculation is applied.

[Flat/FreeCartesianOpen](Flat/FreeCartesianOpen.lean), in
`AlgebraicGeometry.FiniteSchemeNormBaseChange`, supplies
`exists_free_affine_neighborhood_subset_of_isPullback`: the original whole-chart
free cover gives a free affine neighborhood of each chosen point inside any
prescribed open of the actual Cartesian base change. The chart algebra is the
entire inverse image, with the scalar map of its actual projection.

## Isomorphism and boundary-section transport

[Norm/SchemeIso](Norm/SchemeIso.lean) proves `norm_appTop_of_iso` over any
commutative ring `R : Type u`. An actual isomorphism of schemes over `Spec R`
induces the algebra equivalence used by the determinant norm; neither source
needs a domain or reducedness hypothesis. [GenericFiber/LineRatioIso](Norm/GenericFiber/LineRatioIso.lean)
proves `genericFiberLineRatioNorm_eq_of_source_iso` for finite maps to an
integral target and monic pulled-back numerator/denominator. Its isomorphism
must commute both with the generic-base projection and with the original
line-bundle source maps. [LineRatioIdentity](Norm/GenericFiber/LineRatioIdentity.lean)
retains the same quotient under the literal identity pullback. The identity
leg does not take a norm along a parameter-change morphism.

[AffineBoundaryScalarRestriction](Norm/AffineBoundaryScalarRestriction.lean)
separates three uses of section equality. `pullback_scalar_eq_one_of_comm`
needs only a commuting ambient square. `app_eq_one_of_affine_pullback_scalar_eq_one`
turns a scalar equality on the canonical `Spec` chart into equality on the full
inverse-image open. `app_eq_one_of_isPullback_affine_scalar_eq_one` specializes
this to an actual Cartesian boundary. These equalities include nilpotents;
they are stronger than support containment. The R3/R5
[pencil constructors](../../RelativeCurve/Pencils/README.md) use these
transports together with the original free charts.
