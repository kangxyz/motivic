# Unbounded hypercohomology from actual derived Hom

For `C : Type u` with `[Category.{v} C]`, a topology `J` and
`[HasSheafify J AddCommGrpCat.{max v t}]`, the native namespace
`CategoryTheory.Sheaf.Hypercohomology` constructs `freeAbelianSheafFunctor`.
Its value at `X` is the universe-lifted free abelian representing sheaf for
sections at `X`.

With `[HasDerivedCategory.{w} (Sheaf J AddCommGrpCat.{max v t})]`,
`H J K p X` is the group of derived morphisms from that sheaf in degree zero
to the localization of `K` shifted by `p : ℤ`; its carrier lies in `Type w`.
Coefficient maps are postcomposition with the actual shifted localized map,
and restrictions are precomposition with the representing-sheaf map.
`presheafFunctor` and `presheaf` retain these maps. No boundedness or
enough-injectives hypothesis is built into this construction.

| Exact import | Interface |
| --- | --- |
| `Motivic.Aglib.CategoryTheory.Sites.Hypercohomology.Basic` | Representing sheaf, section equivalence, derived-Hom groups and presheaves. |
| `Motivic.Aglib.CategoryTheory.Sites.Hypercohomology.Evaluation` | `evaluationComparison` for a projective representing sheaf, with coefficient universe `max u v`. |
| `Motivic.Aglib.CategoryTheory.Sites.Hypercohomology.EvaluationNaturality` | Compatibility of that comparison with coefficient maps. |
| `Motivic.Aglib.CategoryTheory.Sites.Hypercohomology.Naturality` | Restrictions and naturality on the actual coefficient complexes. |
| `Motivic.Aglib.CategoryTheory.Sites.Hypercohomology.Shift` | Actual shift isomorphisms and their restriction equations. |
| `Motivic.Aglib.CategoryTheory.Sites.Hypercohomology.SheafComparison` | Comparison for a sheaf in degree zero, with coefficient universe `v` and the displayed `HasExt` premise. |
| `Motivic.Aglib.CategoryTheory.Sites.Hypercohomology.FreeSheafMonomorphisms` | Monomorphisms of the actual free abelian representing sheaves under its stated sheafification hypotheses. |

A geometric site supplies its own exact-evaluation proof before using
`evaluationComparison`. The present Suslin–Voevodsky model consumes these
interfaces for `Motivic.motivicCohomology` and its finite-coefficient variant;
its coefficient construction has the [host owner](../../../../Cohomology/SuslinVoevodsky/README.md).

Intended upstream family: `Aglib.CategoryTheory.Sites.Hypercohomology`.
Follow the [candidate policy](../../../README.md), retaining the universes and
hypotheses of the selected lower import.
