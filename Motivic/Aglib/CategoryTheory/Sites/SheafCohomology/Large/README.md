# Ordinary sheaf cohomology with larger coefficient universes

For `C : Type u` with `[Category.{v} C]`, a topology `J`,
`[HasSheafify J AddCommGrpCat.{max v t}]` and
`[HasExt.{w} (Sheaf J AddCommGrpCat.{max v t})]`,
`CategoryTheory.Sheaf.LargeCohomology.H J F n X` is the actual Ext group from
the universe-lifted free abelian representing sheaf to `F`, in degree `n : ℕ`.
Its restrictions use the original representing-sheaf maps.

`ordinaryComparison` compares the presheaf functors when the coefficient and
site-Hom universes agree. `singleComparison` compares with unbounded derived
Hom under its displayed `HasDerivedCategory` premise. `zeroSections` identifies
degree zero with actual sections and preserves restrictions. Mathlib's
`Sheaf.H` and `Sheaf.H'` remain unchanged.

| Exact import | Interface |
| --- | --- |
| `Aglib.CategoryTheory.Sites.SheafCohomology.Large.Basic` | `H`, `presheafFunctor`, `ordinaryComparison` and `singleComparison`. |
| `Motivic.Aglib.CategoryTheory.Sites.SheafCohomology.Large.Naturality` | Original cohomology maps and their naturality. |
| `Motivic.Aglib.CategoryTheory.Sites.SheafCohomology.Large.DegreeZero` | `zeroSections`, natural in the sheaf and site object. |
| `Motivic.Aglib.CategoryTheory.Sites.SheafCohomology.Large.LocalTriviality` | Positive-degree local effacement, retaining `EnoughInjectives` and `J.WEqualsLocallyBijective` where used. |
| `Motivic.Aglib.CategoryTheory.Sites.SheafCohomology.Large.RestrictionSource` | Actual representing-source comparison for a continuous-site adjunction, in native `CategoryTheory.Sheaf.Hypercohomology`. |

The [relative cohomology family](../Relative/Basic.lean) owns the relative
cokernel construction and its original boundary maps and signs. Host consumers
construct ordinary cohomology with transfers and the weight-one ordinary
hypercohomology comparison.

The basic larger-universe Ext construction is supplied by pinned Aglib.
Local naturality, degree-zero, restriction-source and local-triviality leaves
extend it without replacing the underlying representing sheaf or Ext group.
The remaining candidates target `Aglib.CategoryTheory.Sites.SheafCohomology.Large`.
Follow the [candidate policy](../../../../README.md), retaining the actual maps,
Ext premises and coefficient universes of the exact lower import.
