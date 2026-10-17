# Motivic complexes and computations

[Motivic.Cohomology.Motivic](../Motivic.lean) exposes the actual sheafified
Suslin complex of the reduced torus, its ordinary Nisnevich hypercohomology,
and derived finite coefficients. Singular chain degree `r` in weight `q`
occupies cochain degree `q-r`. Keep the original shift sign.

Use [Diagonal](Diagonal.lean) for the characteristic-zero Milnor comparison
and naturality, or [WeightOne](WeightOne.lean) for the ordinary unit-sheaf and
hypercohomology comparisons. These entries are optional computations, not
alternative definitions of cohomology. Exact declarations retain their own
field, universe, `HasExt` and derived-category hypotheses.

Broader characteristic, base-scheme, higher-Chow and spectrum comparisons need
separate proved maps. Strict A1 invariance remains open.
