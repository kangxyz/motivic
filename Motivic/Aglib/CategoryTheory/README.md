# General category and site candidates

These interfaces extend native `CategoryTheory` objects under categorical
hypotheses. Their motivic consumers do not add field or HI assumptions to the
general results. Keep the entire dependency closure general.

| Exact import | Interface and boundary |
| --- | --- |
| `Motivic.Aglib.CategoryTheory.AdditiveFunctorLimits` | Actual limits of additive functors under the stated target limits. |
| `Motivic.Aglib.CategoryTheory.Limits.Shapes.Pullback.CompLift` | The literal lift from the pullback of a composite to the intermediate pullback is itself Cartesian. |
| `Motivic.Aglib.CategoryTheory.AdditiveFunctorAbelian` | Actual additive-functor abelian category and finite-limit/colimit preservation. |
| `Motivic.Aglib.CategoryTheory.AdditiveFunctorAB5` | Specified-size filtered colimits and inherited exactness. |
| `Motivic.Aglib.CategoryTheory.AdditiveFunctorGrothendieck` | Existing separator and AB5 assembled into a Grothendieck structure. |
| `Motivic.Aglib.CategoryTheory.CokernelAdditive` | Additivity descending through an objectwise epimorphic natural transformation. |
| `Motivic.Aglib.CategoryTheory.FullSubcategoryHomotopy` | Actual maps, homotopies, homotopy equivalences and retract additivity. |
| `Motivic.Aglib.CategoryTheory.SheafifyAdditive` | Actual principal-covering-basis, sheafification and universe conditions. |
| `Motivic.Aglib.CategoryTheory.SheafifyLocallyBijective` | Canonical sheafification lift and original unit equation. |
| `Motivic.Aglib.CategoryTheory.Sites.Point.SkyscraperCohomology` | Positive ordinary cohomology of one actual site-point skyscraper, with its exact adjunction and original maps. |

[Large sheaf cohomology](Sites/SheafCohomology/Large/README.md) retains the
existing large-universe Ext construction and its Mathlib comparison.
[Unbounded hypercohomology](Sites/Hypercohomology/README.md) uses actual derived
Hom, with explicit site, coefficient and derived-category universes.
Skyscraper cohomology consumes these general primitives, without a host
cohomology dependency. It does not construct a point family or transfer envelope.

Reflective sheaf cokernels are sheaf colimits, not necessarily objectwise
presheaf cokernels. Additivity in source arrows differs from addition of natural
transformations. Exactness alone does not supply acyclicity or the original
cohomological comparison. Host [transfer sheaves](../../Transfers/Sheaf/README.md)
and their cohomology are current consumers. See the [candidate policy](../README.md).

The canonical-pullback lemma `CategoryTheory.Limits.pullback.isPullback_lift_comp`
requires only a category and the two displayed pullbacks of `b ≫ f` and `f`.
It retains the native `pullback.lift`, proving its square with `b` by
`IsPullback.of_bot`; no comparison object or isomorphism is supplied as a
premise. The immediate consumer is the
[whole boundary-factor transport](../AlgebraicGeometry/ProjectiveLine/README.md)
through the two actual coefficient localizations.
