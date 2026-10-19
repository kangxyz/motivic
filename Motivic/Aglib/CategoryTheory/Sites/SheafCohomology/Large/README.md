# CategoryTheory / Sites / SheafCohomology / Large

Existing Ext bifunctor from the universe-lifted free abelian representing sheaf, compared to actual Mathlib cohomology when coefficient and site-Hom universes agree. Relative cokernels, restrictions, boundaries and naturality retain their original maps and signs.

HasSheafify/HasExt and all existing universe bounds remain explicit. Local triviality retains EnoughInjectives and WEqualsLocallyBijective. Sheaf.H and Sheaf.H prime from Mathlib are not replaced.

| Exact import |
| --- |
| `Motivic.Aglib.CategoryTheory.Sites.SheafCohomology.Large.Basic` |
| `Motivic.Aglib.CategoryTheory.Sites.SheafCohomology.Large.Naturality` |

Native interfaces:

- `CategoryTheory.Sheaf.LargeCohomology.H`
- `CategoryTheory.Sheaf.LargeCohomology.presheafFunctor`
- `CategoryTheory.Sheaf.LargeCohomology.ordinaryComparison`
- `CategoryTheory.Sheaf.LargeCohomology.zeroSections`

Host consumers construct ordinary cohomology with transfers and the weight-one ordinary hypercohomology comparison.

Intended upstream family: `Aglib.CategoryTheory.Sites.SheafCohomology.Large`. Use exact lower
imports; a current motivating consumer does not change the general hypotheses.
Follow the [candidate policy](../../../../README.md) and retain the actual maps and
universes when extending these interfaces.
