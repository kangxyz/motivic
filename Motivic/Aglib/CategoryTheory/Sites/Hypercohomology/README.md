# CategoryTheory / Sites / Hypercohomology

Actual derived Hom from the degree-zero free abelian representable to the localized coefficient complex shifted by an arbitrary integer; maps are actual shifted localized maps, restrictions are precomposition.

Explicit category/site and coefficient universes; HasSheafify; HasDerivedCategory. Exact evaluation requires projectivity of the actual source. No bounded-below hypothesis or enough-injectives premise is inserted.

| Exact import |
| --- |
| `Motivic.Aglib.CategoryTheory.Sites.Hypercohomology.Basic` |
| `Motivic.Aglib.CategoryTheory.Sites.Hypercohomology.Evaluation` |
| `Motivic.Aglib.CategoryTheory.Sites.Hypercohomology.Naturality` |

Native interfaces:

- `CategoryTheory.Sheaf.Hypercohomology.freeAbelianSheafFunctor`
- `CategoryTheory.Sheaf.Hypercohomology.H`
- `CategoryTheory.Sheaf.Hypercohomology.presheaf`
- `CategoryTheory.Sheaf.Hypercohomology.evaluationComparison`

The present Suslin–Voevodsky model uses these interfaces for `Motivic.motivicCohomology` and its finite-coefficient variant.

Intended upstream family: `Aglib.CategoryTheory.Sites.Hypercohomology`. Use exact lower
imports; a current motivating consumer does not change the general hypotheses.
Follow the [candidate policy](../../../README.md) and retain the actual maps and
universes when extending these interfaces.
