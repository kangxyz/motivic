# Names and modules

The Lake package, production library and import root are `Motivic`. The test
library and module root are `MotivicTest`; avoid a generic `Tests` package
that collides with dependencies. Existing test declarations in native object
namespaces are retained where their proofs extend those objects. New test-only
helpers belong in `MotivicTest.<Family>`.

Use PascalCase module components and Mathlib declaration conventions. Name
families by mathematical objects and constructions, not a checkpoint, author's
name, proof attempt, migration lane or future milestone. A new leaf should
have a specific owner; split mixed general/application results when needed by
a real consumer. The imported descriptive leaf names stay valid during this
bootstrap, avoiding unnecessary import and theorem-name churn.

Declaration namespaces follow the object. Extend `CategoryTheory`,
`AlgebraicGeometry`, `Ideal`, and other native owners for their general facts.
Use `Motivic.Cor`, `Motivic.PresheafWithTransfers`, `Motivic.SheafWithTransfers`,
`Motivic.SheafCohomology`, and `Motivic.KTheory.MilnorK` for the actual existing
constructions. `Motivic.Cohomology.Motivic` is an import family, not a new
wrapper namespace or second cohomology type.

Use `map`/`map_id`/`map_comp` for functorial maps, `...Iso` for categorical
isomorphisms and `...Equiv` for the relevant equivalence. Prefer explicit
source/target information when multiple maps or coefficient actions coexist.
Preserve actual graph, restriction, boundary and coefficient maps in comparison
names and statements. A similar-looking replacement object is insufficient.

A family facade contains only precise public imports and its scope comment.
New implementation leaves should import exact lower leaves. Avoid redundant
aliases solely to spell the same native object with a package prefix.
