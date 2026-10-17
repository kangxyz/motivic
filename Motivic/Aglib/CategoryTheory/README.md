# General category-theory infrastructure

These files use native `CategoryTheory` namespaces and general categorical hypotheses.
They are candidates for reuse upstream in Aglib or Mathlib; this directory does not
introduce motivic geometry, correspondences, or homotopy-invariance assumptions.

- `AdditiveFunctorLimits.lean`: limits preserve additivity in source arrows; the
  full subcategory of additive functors inherits the available limits.
- `AdditiveFunctorAbelian.lean`: colimits preserve additivity, and the actual
  category of additive functors into an abelian category is abelian. The
  forgetful inclusion preserves finite limits and colimits.
- `AdditiveFunctorAB5.lean`: colimits and filtered colimits of the stated size,
  with exactness inherited from the abelian target through the fully faithful
  inclusion.
- `LiftedAdditiveYoneda.lean`: actual universe-lifted additive representables,
  their additive Yoneda equivalence, and their coproduct separator. Coefficients
  contain both the source object and source morphism universes.
- `AdditiveFunctorGrothendieck.lean`: combines those exact filtered colimits and
  that separator into a genuine Grothendieck abelian structure.
- `CokernelAdditive.lean`: a narrower proof of additivity descending along an
  objectwise epimorphic natural transformation, including ordinary functor-category
  cokernels, without assuming an abelian additive-functor category.
- `FullSubcategoryHomotopy.lean`: componentwise lifting of actual maps, homotopies,
  and homotopy equivalences to a full subcategory, plus additivity of a retract.
- `ReflectiveColimits.lean`: colimit preservation descends through an actual
  reflection isomorphism. The inclusion need not preserve colimits.
- `SheafifyAdditive.lean`: additivity descends along a locally surjective map to a
  separated presheaf when every covering sieve contains a covering principal
  sieve. The ordinary sheafification consequence keeps its explicit site and
  universe hypotheses.
- `SheafifyLocallyBijective.lean`: identifies an actual locally bijective map to a
  sheaf with the canonical sheafification lift, under the stated local-equivalence
  hypotheses, retaining compatibility with the unit.
- `SplitCokernelKernel.lean`: canonical cokernel-to-kernel comparison for a split
  pair in a preadditive category, using the actual inclusion, projection, and
  quotient maps.
- `Sites/Point/SkyscraperCohomology.lean`: ordinary positive-degree cohomology of
  one actual site-point skyscraper vanishes. Its exact point adjunction retains
  the actual restriction and coefficient maps, using projectivity of the fiber
  of the free section-representing sheaf. It does not construct a point family,
  product envelope, or transfer action.

## Scope and dependencies

The proofs depend on Mathlib category-theory APIs and earlier files in this
cohort. The skyscraper theorem also reuses the existing generic ordinary
cohomology and free-section source in `Motivic/Cohomology/`; it introduces no
replacement source or cohomology provider.
Cokernels in a reflective sheaf subcategory are sheaf colimits; they are
not asserted to be objectwise cokernels of presheaves. Closure under limits or
colimits is used only with the corresponding target-category existence
hypothesis. Additivity of sheafification concerns additive source-arrow actions,
not merely the addition of natural transformations.

The geometric consumers live in `Motivic/Transfers/`; their strict source tests
are separate. This cohort does not supply positive-degree cohomological transfers,
acyclicity of underlying sheaves of transfer-injectives, strict A¹ invariance,
or cancellation.
