# Motivic cohomology foundations

## Recovery status: 17 October 2026

This recovery checkpoint captures source bytes on 2026-10-17 at approximately
04:36:40 UTC. The October 16 snapshot/build statements retained below are
historical, not a new full-project validation. See CHECKPOINT.md for the exact
fresh verification scope and matching success logs.

Fresh strict leaf checks passed for the categorical distinguished-square
infrastructure, the repaired geometric Nisnevich distinguished square, the new
smooth-site distinguished-square adapter and its direct test, and the new
PolynomialNormDVRQuadratic leaf and its direct test. The quadratic test checked
700 transitive norm–residue/Milnor declarations using standard axioms only.

The strengthened PrescribedTrivialization ring leaf and direct consumer, and
the new actual affine line-bundle PrescribedNeighborhood leaf and direct
consumer, also passed fresh strict checks. The latter extends a prescribed
trivialization on a whole closed affine boundary to a principal open
neighborhood, retaining equality of the original pulled-back isomorphism.
No reducedness, connectedness or nonemptiness assumption is imposed on the
boundary. Dependency closure restoration is still in progress.

SquareDifferenceActions remains an unverified repair in progress in this
snapshot. SheafCohomologyH1NisnevichSquareDescent and its test are uncompiled
drafts. General positive-degree strict A¹ invariance and the general
Milnor-to-motivic isomorphism remain incomplete. Neither a clean rebuild nor
fresh validation of the complete public root is claimed.

A Lean library for concrete foundations of the Suslin–Voevodsky programme.
The current checked interfaces include actual finite correspondences over an
arbitrary field, their graph functor, and abelian presheaves with transfers.
The actual reduced transfer torus, all-degree motivic complex, and unbounded
Nisnevich hypercohomology are now constructed, including exact field evaluation.
The complete motivic-cohomology theory is still under development.

## General-degree diagonal interfaces

- `Motivic.KTheory.MilnorK.Basic`, `Map`, and `LowDegree` define the actual
  integral Milnor symbol quotient in every degree over every field, its
  universal property and field maps, and compute degrees zero and one.
  `CompatibilityK2` and `CompatibilityK3` give explicit natural equivalences
  with the existing degree-two and degree-three tensor presentations.
  `Product` and `Symbols` give genuine two-sided quotient multiplication,
  transported associativity and unit laws, and adjacent sign identities.
- `Motivic.Cohomology.Motivic.DiagonalTopDegree` identifies the literal reduced
  torus quotient `C₀ / im(d₁)` with the originally defined derived `H^{q,q}`
  in every weight over every field. The signed cochain differential retains
  `(-1)^q`; only its image is identified with the singular boundary image.
- `DiagonalCycleSymbols`, `DiagonalCoordinateInsertion`, `DiagonalMilnorSymbol`
  and `DiagonalFieldChange` construct the actual forward map from integral
  Milnor K in every degree to the original diagonal motivic group over
  characteristic-zero fields. It sends tuples to their rational graph classes,
  is natural under arbitrary field homomorphisms, and agrees with the original
  weight-one norm and weight-two symbol. Its general bijectivity remains open.
- `DiagonalWeightZero` computes the original integral `H^{0,0}(k)` as `ℤ`
  over every field. The actual structural graph has degree one, signed
  multiples are retained, and the general forward map in degree zero is
  exactly the proved `K₀` equivalence.
- `DiagonalCorestriction` and `DiagonalCorestrictionTower` give actual finite
  extension transfers on raw and derived diagonal groups in every weight,
  including signed finite-point formulas, identity and tower laws. These do
  not yet assert compatibility with a canonical general Milnor norm.
- `MilnorK.ResidueSpecialization` gives specialization in every degree from
  actual DVR data, including arbitrary valuation-linear unit-part twists and
  comparison with the existing degree-two specialization. Specialization
  uses a uniformizer; uniformizer independence is not asserted for it.
  `Residue`, `ResidueChange`, `ResidueCompatibility` and `ResidueDVR` construct
  the actual tame residue in every degree, prove independence of the actual
  DVR uniformizer, and agree on every class with the previous K₂/K₃ maps.
  The last-slot normalization, repeated-uniformizer signs and principal-unit
  vanishing with arbitrary other poles are explicit. No norm law is assumed.
- `Motivic.Aglib.RingTheory.DVRCartierLength` proves the actual nonzero
  principal-quotient length equals normalized DVR order in `ℕ∞`.
  `Motivic.Aglib.AlgebraicGeometry.FiniteCurveBranchOrders` identifies original
  endpoint coefficients with the complete residue-degree-weighted sum of
  normalization branch orders over characteristic-zero fields.

These interfaces are foundations for the general diagonal comparison.
The general Milnor-to-motivic isomorphism, integral norm reciprocity, and
boundary descent are not yet proved. New draft leaves are identified in the
snapshot status rather than included in the checked public root prematurely.

## Usable interfaces

`import Motivic.Cor` exposes the correspondence and transfer interfaces below.
They are also available from `import Motivic`. The public-entry consumer
`Tests/CorPublicImports.lean` checks these imports directly.

- `Motivic.AlgebraicGeometry.Correspondences.Category`: `Motivic.Cor k` is a
  category and a preadditive category. Morphisms are actual signed finite
  correspondence cycles; composition is the incidence Tor pairing. The unit
  laws use the full componentwise diagonal, and associativity holds for all
  signed cycles. Smooth objects may be disconnected or empty.
- `Motivic.AlgebraicGeometry.Correspondences.GraphFunctor`:
  `Motivic.Cor.graphFunctor k : SmoothSite (Spec (.of k)) ⥤ Cor k`.
  Its map is the actual componentwise graph cycle; graph composition is proved
  from the actual incidence geometry and Tor multiplicities.
- `...Correspondences.NisnevichSignedLocalLift`: every signed correspondence
  locally factors through a single smooth Nisnevich covering arrow, on an actual
  pointed smooth-site Nisnevich neighborhood. The equality retains the original
  signed Tor composition.
- `...Correspondences.NisnevichFamilyLocalLift`: for an arbitrary Nisnevich
  covering family, every signed correspondence locally equals a finite sum of
  correspondences followed by the covering graphs. The finite list can repeat
  labels, and the full family can be infinite or empty. Actual incidence Tor
  weights and finite-image residue degrees are retained.
- `...Correspondences.NisnevichCechSupportPairing`: two actual target maps from
  one integral support with the same image give a correspondence to the Čech
  fiber product whose projections are the original degree-weighted images.
  The whole coefficient cycle is retained in the subsequent local exactness theorem.
- `...Correspondences.NisnevichCechLocalExactness`: a signed correspondence
  whose composite with a Nisnevich graph is zero becomes an actual Čech
  boundary on a pointed Nisnevich neighborhood. The proof retains the complete
  incidence Tor coefficient function and signed cancellations in the actual
  common finite closed support; no perfect-field hypothesis is added.
- `...Correspondences.BinaryCoproducts`: the actual finite disjoint unions are
  biproducts in `Cor k`, with their genuine graph inclusions. The actual empty
  scheme is a zero object. The full componentwise diagonal gives the projection
  identities, so disconnected and empty schemes are included.
- `Motivic.AlgebraicGeometry.SmoothSiteFiniteCovers`: a Nisnevich family over a
  Noetherian smooth object has an actual finite disjoint-union total cover,
  retaining the selected original maps and actual residue-field isomorphisms.
- `...Correspondences.NisnevichTopology`: covering sieves on actual `Cor k`
  contain the graph of a genuine singleton Nisnevich cover. Signed local lifting
  and actual finite disjoint unions prove pullback stability. This has a
  principal covering basis; it does not assert unrestricted graph-functor
  continuity for nonadditive presheaves.
- `...PresheavesWithTransfers.NisnevichComparison`: an additive presheaf is a
  sheaf on the actual correspondence Nisnevich site exactly when its graph
  restriction is an ordinary smooth-site Nisnevich sheaf. This uses the genuine
  local Čech boundary theorem and finite disjoint unions, and includes arbitrary
  covering families and the empty scheme. Coefficient universes are independent.
- `...PresheavesWithTransfers.NisnevichSheafification`: actual transfer-preserving
  Nisnevich sheafification is additive and left adjoint to the original
  inclusion of sheaves with transfers. Its canonical unit is natural for all
  signed correspondences. Forgetting transfers recovers ordinary Nisnevich
  sheafification by a natural isomorphism identifying the canonical units.
  For a field in `Type u`, the usable construction has coefficient universe
  `u + 1`; public consumers synthesize all required Mathlib instances.
- `Motivic.AlgebraicGeometry.PresheavesWithTransfers.Basic`: additive
  contravariant functors from `Cor k` to abelian groups, with transfer laws.
- `...PresheavesWithTransfers.Representable` and `...Yoneda`: the fully faithful
  additive representable embedding and additive Yoneda equivalence.
- `...PresheavesWithTransfers.GraphRestriction`: faithful additive restriction
  to ordinary smooth-site presheaves along the graph functor.
- `Motivic.AlgebraicGeometry.SmoothSiteProducts`: literal relative scheme
  products and their canonical comparison with categorical products.
- `...Correspondences.SimplexExterior`: `Cor.simplexExterior n` sends signed
  correspondences to actual correspondences between products with the
  barycentric simplex. Its generator cycle is the finite pushforward of the
  fundamental cycle of the actual product support. The simplex is proved
  geometrically integral over its original base.
- `...Correspondences.ProductGraphTransversality`: a genuine mixed-product
  pullback and a common regular diagonal list for arbitrary parameter maps.
  Neither the support map nor the parameter map is assumed flat.
- `...Correspondences.SimplexExteriorGraphInterchange`: exterior extension
  commutes with the actual graph of every map between geometrically integral
  smooth parameters. This includes all original simplex faces and degeneracies,
  with arbitrary signed correspondence coefficients.
- `...Correspondences.SimplexSingularTransferMaps`: every actual signed
  correspondence induces an all-degree singular chain map. Its degreewise map
  is transfer along the original exterior cycle, and it commutes with the
  alternating-coface differentials. The maps are additive, including negative
  and integer multiplicities.
- `...Correspondences.SimplexExteriorFunctor`: the actual signed exterior
  cycles preserve identities and composition, giving the additive endofunctor
  `Cor.simplexExteriorAdditiveFunctor k n` on arbitrary smooth objects.
- `...Correspondences.SimplexSingularTransferFunctor`: for every presheaf with
  transfers, `PresheafWithTransfers.singularAdditiveFunctor` is an additive
  contravariant functor from actual correspondences to the full singular chain
  complexes. Its maps are the original degreewise transfers; identity and
  composition are proved, including signed correspondences.
- `...Correspondences.ExteriorIdentityIncidence`: adjoining an identity
  parameter preserves the full incidence scheme, including its nilpotents.
  `...ExteriorPointClosurePushforward` retains the original finite-map residue
  degree in the product fundamental-cycle pushforward.
- `...Correspondences.ExteriorIdentityTorLengthComparison`: every actual exterior
  incidence Tor length is the original Tor length times the entire local closed-
  fiber length. The same formula holds for the original generic Tor coefficient;
  all nilpotents and higher Tor terms are retained. `ExteriorIdentityTorCycle`
  assembles this into the actual full incidence cycle, and
  `ExteriorIdentityComponentPushforward` retains the original residue degrees
  under its component pushforwards. `ExteriorIdentityComposition` proves
  preservation of the actual incidence pairing for all signed correspondences,
  including `Cor.simplexExterior_comp`.
- `Motivic.Algebra.Homology.KoszulRegularBlockElimination`: removes a proved
  regular leading block through its actual quotient map, preserving every
  remaining Koszul homology module and its original scalar action.
- `Motivic.AlgebraicGeometry.SmoothSiteNisnevich` and `...Refinement`: the
  actual smooth Nisnevich topology, with the usual residue-field covering
  criterion. Over any affine base it agrees with the restricted and induced
  big-site topology; the inclusion is continuous and cocontinuous.
- `...SmoothSiteNisnevichSheavesWithTransfers`: `SheafWithTransfers k`, with
  a faithful additive underlying ordinary-sheaf functor.
- `...SmoothSiteNisnevichSheafification`: canonical ordinary sheafification
  commutes with big-to-small restriction, with its unit formula and explicit
  sheafification/right-Kan-extension size hypotheses.
- `...Correspondences.FiniteSupportShrinking`: simultaneous open shrinking
  for the entire actual finite support of a signed correspondence.
- `Motivic.Aglib.RingTheory.HenselianEtaleSections`: prescribed residue-field points
  of arbitrary étale algebras lift over henselian local rings, including
  nonreduced local Artinian bases.
- `Motivic.Aglib.RingTheory.ArtinianEtaleSections`: prescribed points at every maximal
  ideal lift simultaneously over a whole Artinian base, including nonlocal,
  nonreduced and zero rings. The proof uses a nilpotent formally-smooth lift.
- `Motivic.Aglib.AlgebraicGeometry.HenselianEtaleSections`: a specified
  residue-field point of any étale scheme over a henselian local ring lifts to
  a section with the same reduction, without requiring the total scheme affine.
- `Motivic.Aglib.AlgebraicGeometry.Sites.NisnevichHenselian`: actual Nisnevich
  covers over henselian local and local Artinian spectra contain split members;
  their covering sieves are maximal. The local Artinian base may be nonreduced.
- `...Sites.NisnevichHenselianEvaluation`: ordinary sheafification is unchanged
  on henselian-local sections, with explicit universe and sheafification
  hypotheses. Abelian Nisnevich-sheaf evaluation there preserves exact sequences
  and homology.
- `Motivic.Aglib.AlgebraicGeometry.ArtinianEtaleSections`: an arbitrary étale
  scheme over a locally Artinian base admits a whole-base section when each
  residue field admits a rational lift. This includes disconnected, nonreduced,
  and empty bases.
- `Motivic.Aglib.AlgebraicGeometry.NisnevichQuasiFinite`: a quasi-finite branch
  of a separated morphism admits a genuine pointed Nisnevich neighborhood with
  a finite clopen piece and singleton distinguished fiber. The isomorphism is
  the neighborhood morphism's actual residue-field map.
- `Motivic.Aglib.AlgebraicGeometry.NisnevichFiberSections`: a Nisnevich-surjective
  étale morphism lifts every map from a locally Artinian scheme, hence the whole
  actual fiber of a locally quasi-finite morphism. Finite-support neighborhood
  descent is supplied by the separate theorem below.
- `Motivic.Aglib.AlgebraicGeometry.NisnevichFiniteSplitting`: every finite
  morphism splits on a pointed Nisnevich neighborhood into a complete finite
  disjoint clopen partition, each piece with singleton distinguished fiber.
  This retains nonreduced structure and handles an empty original fiber.
- `Motivic.Aglib.AlgebraicGeometry.FiniteEtaleNeighborhoodIso`: a finite étale
  map with singleton fiber and an isomorphic actual residue-field map is an
  isomorphism on a Zariski neighborhood. The base need not be reduced or connected.

- `Motivic.Aglib.AlgebraicGeometry.NisnevichFiniteBranchLift`: a separated étale
  rational lift at the unique point of a finite fiber extends to a lift of the
  entire pulled-back support over an actual pointed Nisnevich neighborhood.
  The support need not be flat or reduced; its residue extension may be inseparable.

- `Motivic.Aglib.AlgebraicGeometry.NisnevichFiniteLifting`: for an arbitrary
  finite support, residue-compatible lifts through a separated étale map at
  every point of one fiber extend simultaneously over a pointed Nisnevich
  neighborhood. The resulting morphism lifts the whole actual pulled-back
  support, including disconnected, nonreduced, and empty fibers.

The new consumers include signed and integer multiplicities, disconnected/empty
objects, literal cycle formulas, naturality and reuse of the existing ordinary
singular-presheaf construction. The actual simplex exterior and all-degree
singular transfer functors are proved. Transfer-preserving Nisnevich
sheafification, its left adjunction, and its canonical ordinary underlying
comparison are now constructed from actual local Čech exactness, finite cover
normalization and the correspondence topology. The sheaf-condition comparison
is proved for additive presheaves.
The separate classical ambient-Tor
comparison draft is not needed by these interfaces and is not asserted to pass.

A reusable checked lemma in
`Motivic.Aglib.CategoryTheory.SheafifyAdditive` proves that ordinary Mathlib
sheafification preserves addition of source-category arrows on a site with a
basis of principal covering sieves. Its sheafification hypotheses and coefficient
universe are explicit. Its application to the actual correspondence topology passes the consumer
checks. The sheaf-condition comparison identifies these additive sheaves with
the original category of ordinary Nisnevich sheaves with transfers. The bundled
sheafification functor, its adjunction, and comparison of its underlying unit
with ordinary sheafification are checked.

## Actual motivic complexes and cohomology

`import Motivic.Cohomology.Motivic.Complex` exposes the actual canonical
construction; `import Motivic.Cohomology.Motivic.Hypercohomology` also exposes
its derived cohomology. Both are available from `import Motivic`.
`import Motivic.Cohomology.Motivic.FieldCycleEvaluation` supplies the concrete
cycle-complex evaluation theorem and is also exported by the public root.

- `SmoothSite.torusPower` is the actual relative power of the Laurent spectrum.
  Every identity-axis inclusion is the genuine coordinate map, with a deletion
  retraction and a closed-immersion proof, over arbitrary commutative rings.
- `PresheafWithTransfers.reducedTorus k q` is the quotient of the actual
  signed-cycle representable of this torus by the sum of all identity-axis
  images. Its pointwise quotient, universal property, signed transfer formula,
  weight-zero base representable and weight-one identity-section cokernel are
  proved.
- `motivicComplex k q` is the genuine signed Mathlib shift by `-q` of the
  degreewise transfer-Nisnevich-sheafified singular complex of this quotient.
  Every singular degree is included. The comparison to degree `q-r` has
  component sign `(-1)^(q*r)`; the weight-two differential from degree one to
  degree two is precisely sheafified `face_0 - face_1`. Weight one retains its
  necessary negative shift sign. The differential squares to zero, and terms
  above the weight vanish.
- `motivicCohomology k p q X` is actual unbounded derived-Hom Nisnevich
  hypercohomology of the underlying ordinary sheaf complex. Its derived
  localization universe is explicit; the standard large derived category
  supplies an unconditional instance. Pullback along smooth-site maps is
  functorial.
- `motivicBaseEvaluationComparison` identifies this derived group at the
  actual base object `Spec k` with cohomology of the evaluated sheaf complex,
  in every integer degree. The proof uses split Nisnevich covers of the base
  and the projective sheaf representing its sections. It does not treat an
  arbitrary field extension as a finite-type object of the original site.
- `motivicRawBaseEvaluationComparison` further identifies the same derived
  field group with homology of the literal reduced-transfer singular complex
  before sheafification, genuinely shifted by `-q`. The entire evaluated
  sheafification unit is proved to be a cochain isomorphism, so every
  differential and sign is retained.

- `Motivic.AlgebraicGeometry.PresheavesWithTransfers.SingularNormalization`
  constructs the full simplicial transfer object, including degeneracies, and
  its actual Moore normalization. Inclusion, retraction and both homotopies
  respect signed transfers. Additive sheafification, cochain placement and the
  genuine signed shift preserve this homotopy equivalence, including for the
  canonical motivic complex. No abelian-category assumption on sheaves with
  transfers is used to obtain the homotopies.
- `Motivic.Cohomology.Motivic.FiniteCoefficients` defines
  `motivicFiniteComplex k q n` as the actual transfer-sheaf cone of
  multiplication by `n` on `motivicComplex k q`. It has the distinguished
  coefficient triangle in the homotopy category, positive Bockstein, and reduction/insertion maps for
  composite levels, and a genuine contraction at level one. Forgetting
  transfers gives the ordinary sheaf coefficient cone by an actual isomorphism.
  The construction allows coefficients divisible by the field characteristic.

- `Motivic.Cohomology.Motivic.FiniteHypercohomology` supplies the actual
  finite-coefficient derived groups and smooth-scheme restriction maps. At
  the base field, their evaluation is canonically the cohomology of the
  coefficient cone of the integral field complex. The transported integral
  reduction and positive Bockstein have explicit comparison formulas and
  form the exact sequence `H^p --n--> H^p --> H^p_n --> H^(p+1) --n--> H^(p+1)`.
  The canonical evaluated quotient-to-torsion sequence is short exact; level
  one gives the zero derived field group. No invertibility assumption on `n`
  is needed. This field statement does not assert a general-scheme long exact
  sequence.

These definitions and convention comparisons work over arbitrary fields.
The field weight-one computation is described below. The full sheaf-level
weight-one comparison, weight-two computation, Zariski/Nisnevich comparison,
products and arithmetic comparison theorems remain separate mathematical targets. The existing coefficient-cone algebra has not
yet been identified here with a derived tensor functor.

## Arbitrary field changes and the first norm calculation

`FiniteCorrespondence.fieldBaseChange` is a genuine additive map on signed
finite correspondences for every field homomorphism `k →+* L`. It pulls back
the whole scheme-theoretic support and uses the lengths at all its generic
points, so inseparable nilpotents and component splitting retain their actual
multiplicities. The complete graph cycle and identity cycle are preserved,
including disconnected and empty sources. Compatibility with arbitrary signed
correspondence composition is proved through the full actual incidence Tor
cycle and its finite pushforward. `Cor.fieldBaseChange φ` is an additive
functor, also bundled as `Cor.fieldBaseChangeAdditiveFunctor φ`. No finite-type
or separability condition is imposed on the field extension.

The actual simplex comparison is natural for all faces and degeneracies.
The Laurent torus and every torus power commute with coefficient change,
retaining their coordinate units and every identity-axis insertion. These
scheme comparisons allow arbitrary ring maps. Their field specializations
impose no finite-type or separability condition on the extension.

`Motivic.Aglib.RingTheory.FiniteAlgebraNormLength` computes the determinant
norm of every element of a finite-dimensional commutative field algebra as
the product of the residue-field norms raised to the actual local lengths.
The proof derives finiteness before converting lengths to natural numbers.
This includes nonreduced, disconnected and zero algebras. It is an algebraic
input for the weight-one calculation below.

The reusable `Motivic/Aglib/AlgebraicGeometry/FlatFundamentalCycle` theorem
expands a whole product fundamental cycle over a field as the finite double
sum over original reduced component supports, with both original local
lengths and the unreduced pair products retained.
`ClosedImmersionKoszulEuler` proves that a finite signed equality of pushed
closed fundamental cycles gives the same fixed-list Euler equality whenever
the actual local Artinian cut and maximal-ideal conditions hold. These are
inputs in the completed field-change composition proof.

## Point norms and the flat-fiber comparison

The actual weight-one point-cycle norm now descends through the identity-axis
cokernel defining the reduced torus. Its value on the graph of a unit is that
unit, and the descended norm is surjective. `WeightOneBoundaryNorm` proves
that it kills every actual reduced singular boundary, retaining the canonical
weight-one minus sign. `WeightOneHomologyNorm` descends it to actual raw
homology and then to the defined derived group `H^{1,1}(Spec k, Z)`. The norm
to `kˣ` is surjective via actual graph classes over every field.
`WeightOneEquivalence.weightOneEquiv` proves the resulting actual
`H^{1,1}(Spec k, Z) ≃+ Additive kˣ`. Its forward map is precisely this norm,
and its inverse is the original rational graph class transported through the
proved derived-to-raw comparison. No separability or characteristic hypothesis
is imposed. This is the field group computation; a full sheaf-level
weight-one quasi-isomorphism is a separate theorem.

`WeightOneFiniteCoefficients.weightOneFiniteEquiv` computes the actual
`H^{1,1}(Spec k, Z/n)` as the literal quotient `kˣ/(kˣ)^n`. The original
integral reduction maps the geometric norm to its own unit coset; the inverse
is the reduction of the original graph class. Every positive level is covered,
including one, composite levels and levels divisible by the characteristic.
The proof derives integral `H^{2,1}=0` from the actual raw complex and uses the
existing coefficient exact sequence. Tests also prove the actual class of
`-1` over the rationals is nonzero at level two. Degree-zero finite groups
and a roots-of-unity comparison are separate questions.

`PolynomialFiberNorm` proves determinant norm base change and constancy of the
norm of a global unit in any finite free algebra over `k[t]`. Its endpoint
formula includes every residue-field norm with the full local-ring length.
Finite torsion-free polynomial algebras satisfy the same statement by the PID
free-module theorem.

`FlatLeftGraphComposition` proves that a finite correspondence whose source
projection is flat has no positive actual incidence Tor. Precomposing it by a
graph from an integral smooth source gives the finite pushforward of the
fundamental cycle of the literal scheme-theoretic fiber. This applies to both
simplex endpoints and retains nonreduced multiplicities. The geometric norm
attachment and all-boundary calculation are proved downstream.

The field-change composition theorem joins the actual whole-incidence Koszul
coefficient comparison, same-list component-pair Euler expansion, transport of
the original smooth diagonal list, and all-branch finite pushforward with the
original residue degree. Nongeneric vanishing and finite-image collisions are
handled before the final equality of signed correspondence cycles.

`WeightOneFundamentalNorm` identifies the actual norm of a finite fundamental
correspondence with determinant norm on its whole coordinate algebra. Every
maximal branch and nonreduced stalk length remains present.
`MonicUnitInterpolation` constructs the finite free interpolation algebra
between a monic polynomial and its norm/identity split target, with explicit
whole endpoint-fiber equivalences. The actual interpolation family and whole
endpoint cycles have been constructed. Finite-flat curve specialization is
proved by the actual singleton Cartier cut, retaining original generic and
nonreduced fiber lengths. The split endpoint cycle counts coincident roots
with their full multiplicity. Actual closed-point generators have their
minimal-polynomial support presentations. Interpolation gives the complete
kernel computation, and quadratic interpolation proves multiplication of
units corresponds to addition of graph classes in the original homology.

## Source organization

General algebraic geometry and reusable algebraic lemmas suitable for Aglib
are developed under `Motivic/Aglib/`. Their current consumers import those
modules directly. This is local organization for future upstream contributions;
only the pinned Aglib dependency below is imported from upstream.
Correspondences, transfers and motivic constructions remain in their own
`Motivic/` families. Existing unrelated modules are classified gradually.

## Pinned dependencies

- Lean `4.34.1`
- Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`
- Aglib `40af743ab794d607f566cec0c5417d8e4d02a735`

Aglib is a real pinned Lake dependency. The seven former local R5Lab leaves are
now import/name adapters to its native modules. Historical attribution is in
`THIRD_PARTY_NOTICES.md`; no R5Lab or Quillen package is imported.

## Build

Keep the committed toolchain and manifest. Lake materializes those pinned
dependencies when needed. In a new checkout, obtain their official caches:

```sh
lake exe cache get
python3 .lake/packages/Aglib/.github/actions/lake-cache/cache.py \
  --root . restore --repositories kangxyz/aglib
lake --rehash --no-build build \
  @Aglib/+Aglib.RingTheory.Multiplicity.PrincipalEuler.Associativity:olean
```

The official restore helper may succeed on a cache miss; the last command checks
that the selected native artifact is actually available. Existing unchanged
artifacts should be reused; no cache purge or fresh rebuild is needed.
Build the desired project entry and consumers normally:

```sh
lake build Motivic.AlgebraicGeometry.Correspondences.Category
lake build Motivic.AlgebraicGeometry.Correspondences.GraphFunctor
lake build Motivic.AlgebraicGeometry.PresheavesWithTransfers.GraphRestriction
lake build Motivic.Cor
lake build Tests.CorPublicImports
lake build Tests.CorIntegration
lake build Motivic.Cohomology.Motivic.Hypercohomology
lake build Motivic.AlgebraicGeometry.Correspondences.FieldBaseChangeComposition
lake build Motivic.Aglib.RingTheory.FiniteAlgebraNormLength
lake build Tests.MotivicIntegration
```

For an existing checked project cache, a direct strict integration check is:

```sh
lake env lean -j1 -DautoImplicit=false -DmaxHeartbeats=200000 \
  -DwarningAsError=true -Dweak.linter.mathlibStandardSet=true \
  Tests/CorIntegration.lean

lake env lean -j1 -DautoImplicit=false -DmaxHeartbeats=200000 \
  -DwarningAsError=true -Dweak.linter.mathlibStandardSet=true \
  Tests/MotivicIntegration.lean
```

`bash scripts/check-file.sh Module/Path.lean` checks one changed leaf;
`python3 scripts/build-missing-project.py Module.Name` restores only absent
project artifacts in dependency order. The latter does not detect stale edited
sources. Both use the existing pinned dependency artifacts and all standard
source linters. Check affected dependants after changing a library source.

## Actual field maps on motivic groups

`RawFieldChange` changes actual signed cycles through the full identity-axis
quotient and every simplex operator. Its cochain map retains the original
weight-dependent shift signs in every integer degree.
`FieldCohomologyChange` transports that map to the genuinely defined derived
integral and finite groups at each field's own base object. The original
integral reduction and positive Bockstein commute with arbitrary field maps,
for every natural coefficient level. No finite-type or separability assumption
on the extension is required.

`WeightOneNormFieldChange` proves the original point norm commutes with this
map on all signed cycles and reduced-torus sections. It retains the whole
pulled-back finite scheme and all local lengths. `WeightOneCohomologyFieldChange` proves that the actual integral `H^{1,1}`
equivalence commutes with the ordinary map on units, and the finite equivalence
commutes with the induced map on units modulo powers. These actual weight-one
maps satisfy identity and composition laws. `FieldChangeCoherence` now proves
identity and tower laws for all original signed correspondence cycles under
the literal canonical ambient comparisons, retaining every whole-pullback
component multiplicity. `RawFieldChangeCoherence` proves identity and arbitrary-tower laws for the
original raw cochain maps, their zero extension and signed shift, the actual
evaluated integral complexes, and the actual derived integral and finite
cohomology maps in all bidegrees. The finite statements hold at every natural
coefficient level, including levels divisible by the characteristic. A sheaf
inverse-image comparison remains a separate interface.

## Field top degree and finite coefficients

`FieldTopDegree` proves that actual integral and finite base-field groups vanish
for `p > q`. In top degree, the original integral reduction induces the canonical
isomorphism `H^{q,q}(k, Z/n) ≃ H^{q,q}(k, Z)/n`, with its exact coset formula.
This holds for every natural level and every field; it does not compute the
integral top group or assert a Milnor K-theory comparison.

## Genuine weight-two symbols

`WeightTwoSymbols` constructs a bilinear rational-point symbol and its tensor
homomorphism from `Additive kˣ ⊗[ℤ] Additive kˣ` into the actual integral
`H^{2,2}(k, Z)`. The proof uses finite-flat polynomial families, retaining
coincident-root multiplicities. `WeightTwoFiniteSymbols` applies the original
coefficient reduction and proves the literal graph, cone and top-degree
quotient formulas, together with annihilation by `n`. These statements include
composite and characteristic-dividing levels. The Steinberg relation below is
proved in characteristic zero; the Milnor `K₂` comparison map and its surjectivity are proved below, while injectivity remains open. `WeightTwoFieldChange` proves that the original
integral and finite tensor symbols commute with the actual derived field maps,
using the ordinary field map on each unit tensor factor.
`WeightTwoSkewSymmetry` uses diagonal postcomposition of the genuine quadratic
family to prove skew symmetry of the integral and finite symbols. A repeated
coordinate is proved to be 2-torsion; this is not an alternation assertion.

`Motivic.Aglib.RingTheory.TwoUnitPolynomialFamily` supplies the finite-free,
faithfully-flat two-unit cubic and its whole tensor fibers. In characteristic
three an explicit nonzero nilpotent is retained. `WeightTwoCubicBoundary`
constructs its actual closed `(t,x,1−x)` correspondence and proves equality
of the whole `X³−a³` and `(X−a³)(X²−X+1)` endpoint classes in weight-two
raw homology. Only `a ≠ 0` and `a³ ≠ 1` are assumed. The characteristic-three
case with `a³+1=0` is tested, with repeated-root multiplicities retained.
`FiniteFlatCurveFamily` provides the whole-family graph-restriction adapter.
`WeightOneFinitePointNorm` proves the determinant norm formula for the actual
finite pushforward of an arbitrary extension-field unit point, retaining the
full degree over its coordinate image field. It imposes no separability or
closed-immersion condition. `WeightTwoMixedNorm` then identifies an arbitrary
signed point cycle with a fixed added coordinate with the symbol of its original
norm, using actual polynomial endpoint boundaries. Both left and right mixed
formulas retain the full extension degree. `WeightTwoCorestrictionHomology` now constructs finite-extension
corestriction on the original raw and actual derived `H^{2,2}`, using the
proved literal endpoint compatibility. `WeightTwoCorestrictionMixed` proves
the two mixed-symbol determinant-norm formulas; `WeightTwoCorestrictionDegree`
proves corestriction after the actual field-change map is multiplication by
`[E:k]` on every original raw and derived `H^{2,2}` class. These results allow
arbitrary finite extensions, retaining nonreduced scalar fibers.
`WeightTwoCorestrictionFinite` descends this actual map to `H^{2,2}(-, Z/n)`
through the proved top-degree coefficient comparison, for every natural level.
It commutes with the original integral reduction and retains the signed-cycle
formula.

`WeightTwoSplitPolynomialCycle` proves the entire three-linear-factor cycle
is the sum of its three rational graphs, including collisions and their original
local lengths. `WeightTwoSteinbergBound` applies the actual cubic endpoint
boundary to obtain a universal bound of twelve; the whole cubic and quadratic
quotients retain their true residue degrees. `WeightTwoSteinbergTorsion`
removes a positive universal bound using the entire polynomial `X^n-a`, so
`graphSymbol_steinberg` proves the actual complementary-unit relation over
every characteristic-zero field. `WeightTwoSteinberg` transports this through
the original field-evaluation comparison and coefficient reduction, proving
Steinberg in actual integral `H^{2,2}` and in `H^{2,2}(-, Z/n)` for every natural
level. Rational-symbol generation is now proved below. The Milnor comparison
isomorphism and its inverse remain open.

`WeightTwoMilnorSymbol` now constructs the actual additive maps
`K₂(k) → H^{2,2}(k, Z)` and `K₂(k)/n → H^{2,2}(k, Z/n)` over
characteristic-zero fields, using the original tensor/Steinberg quotient.
The literal graph-symbol formulas, integral reduction squares and arbitrary
field-homomorphism naturality are proved for every natural coefficient level.
Their surjectivity is proved in `WeightTwoMilnorSurjective` below. Injectivity
is not yet proved.

The local `Motivic/KTheory/MilnorK2` modules reuse the original standard
Milnor tensor/Steinberg quotient, field maps, and residue/specialization leaves.
Their private-source rights exceptions and
exact provenance are recorded in `THIRD_PARTY_NOTICES.md`; the standalone
Apache license does not relicense these seven copied implementations.

## Finite-curve Cartier projection

`Motivic.Aglib.AlgebraicGeometry.FiniteCurvePushforwardSpecialization` proves
that a finite surjective map of integral curves over the affine line commutes
with the actual endpoint cut on whole fundamental cycles, with its original
generic residue degree. The proof derives flatness of each curve over the line;
it does not impose flatness of the map between curves, normality, separability,
or reduced endpoint fibers. The whole finite algebra, every source branch,
its actual residue degree and its full local quotient length are retained.
`ScalarExtensionEndpointFiber` and `ScalarExtensionSimplexEndpoint` identify
the literal whole endpoint fibers under scalar restriction. Together these
supply `WeightTwoCorestrictionBoundary.cyclePushforward_face`, which proves
endpoint compatibility on every original signed correspondence, and hence
the homology-level corestriction above.

`Motivic.Aglib.RingTheory.AdjoinRootNormEvaluation` identifies the norm of
`a-root` in the entire monic quotient algebra with the original polynomial's
evaluation at `a`. It retains reducible and nonreduced algebras, including the
constant-monic zero algebra. In particular, the complement has norm `p(1)`;
no chosen root field is substituted for the whole quotient.

## Current verification

On 2026-10-16 the exact Aglib native Linux/Lean cache was restored and verified
with Lake. The tested adapted closure, actual Cor/associativity consumers and
new graph/transfer library and test files passed strict Lean checks. The next
checked additions construct simplex exterior cycles, the actual mixed graph
law, exterior functor and full singular transfer functor, the smooth Nisnevich
site, and the general
henselian/Artinian lifting and local-object results described above. After the
main dependency switch, `Tests/CorIntegration.lean` passed in the main root's
real Lake environment, importing all these consumers together and rejecting
nonstandard axioms reachable from the public interfaces. The allowed logical
axioms are `propext`, `Classical.choice` and `Quot.sound`.

`Tests/MotivicIntegration.lean` also passed in the real pinned Lake environment.
It imports the public root together with the correspondence consumers, actual
torus and quotient constructions, transfer singular and sheaf complexes,
signed-shift dictionaries, derived motivic groups and the exact base-field
evaluation theorem. Its reachable public interfaces use only the same standard
logical axioms.

The checks used one thread per compiler and 200000 heartbeats. Existing project
artifacts were reused where their source/dependency cohort was unchanged.
A clean whole-project `lake build` was not run; direct-Lean project artifacts
have not been promoted to synthetic Lake build traces. The full source package
also preserves unfinished work, so this is not a claim that every possible
optional module is finished.

`WeightTwoCorestrictionTower` proves identity and finite-extension tower laws
for the actual signed cycles, raw homology, derived integral weight-two groups
and every finite coefficient level. The original finite image supports and
residue degrees are retained, without a separability assumption.

## Degree-three Milnor residue prerequisites

`Motivic.KTheory.MilnorK3.Residue` constructs the actual nested tensor/Steinberg
quotient and a sign-correct residue into the original Milnor K₂. Its cyclic
formula, both adjacent Steinberg relations, uniformizer normalization and
repeated-uniformizer signs are proved. `ResidueChange` proves independence from
changing normalized unit parts. `MilnorK3.DVR` instantiates these results from
an actual discrete valuation ring, its fraction field and literal residue map;
its public residue is independent of the irreducible uniformizer chosen.

The reused original `MilnorK2.DVR` sources construct the required elementary
valuation data and prove the unit-part change, rather than supplying residue
laws as assumptions. Their rights exceptions are listed above. The reusable
`Motivic.Aglib.RingTheory.PolynomialLocalResidue` identifies the actual
localization at an irreducible polynomial with a DVR whose fraction field is
`RatFunc k`, and its residue field with the original `AdjoinRoot p`. It proves
literal reduction/evaluation, the localized polynomial uniformizer and the
unit property of reduced-degree representatives, without separability.

These support the actual polynomial-presentation Milnor norms and rational
reciprocity constructed below. The weight-two comparison isomorphism remains
open because the Milnor-valued inverse on arbitrary cycle boundaries is pending.

`MilnorK3.PolynomialResidue.residueAt` now gives the actual map
`K₃(k(t)) → K₂(k[t]/(p))` at every irreducible polynomial. Its normalization
uses literal rational-function units and original polynomial quotient units;
it vanishes on triples of polynomial entries prime to `p`. The adjacent skew,
cyclic and Euclidean identities used for subsequent degree reduction are
proved in `MilnorK3.Symbols`, retaining the repeated-entry sign term.


## Actual finite residues and polynomial degree stages

`MilnorK3.ResidueSupport` proves finite support for the residues of every actual
class in `K3(RatFunc k)` and constructs the dependent finite-residue map to the
original `K2(AdjoinRoot p)` groups. The support is derived from literal
numerators and denominators and then from the nested quotient's symbol
extensionality; no finite-support premise is imposed.

`DegreeFiltration`, `StageLift`, `DegreeGeneration` and `StageEquivalence` prove
reduced-representative multiplicativity and Steinberg descent, construct the
actual residue-field sections, and identify each positive-degree quotient
stage with the dependent finite sum of its actual residue-field K₂ groups.
The filtration exhausts all K₃ classes; its first stage is exactly the image
of constant K₃. Leading coefficients and repeated-entry sign terms are retained.
The stage equivalence explicitly requires positive degree.

`InfinityResidue` uses the actual rational-function automorphism `X ↦ X⁻¹`
and the finite residue at `X`. It kills the entire constant K₃ image, has
positive normalization on `X⁻¹` and negative normalization on `X`, and
`InfinityDegree` proves the formula `∂∞{p,a,b} = −deg(p)·{a,b}` for every
nonzero polynomial and two constant units over any field. Generic inversion
and polynomial reversal are isolated under `Motivic/Aglib/FieldTheory`.

`RationalExactness` identifies the actual finite-residue kernel with constant
K₃ and proves surjectivity. `PolynomialNorm` uses this exactness and the actual
infinity residue to construct the norm for each monic irreducible presentation,
with rational reciprocity. `PolynomialNormBaseChange` proves the full branch
formula under coefficient field changes in characteristic zero, while
`PolynomialNormProjection` proves the ordinary-unit mixed projection formula.
Presentation independence and unrestricted Milnor norm towers are separate
from these polynomial-presentation constructions.


## Full norm comparison and weight-two surjectivity

In characteristic zero, `WeightTwoMilnorNormComparison.raw_norm` identifies
this constructed polynomial norm on every actual K₂ class of a monic
irreducible root field with the original geometric corestriction after the
Milnor symbol map. `derived_norm` and `finite_norm` give the same equality in
the originally defined derived integral group and at every natural coefficient
level. Both coordinates may be arbitrary root-field units.

The proof uses actual low-total-degree generation of K₂, a full finite free
monic deformation, and strong induction on the polynomial degree. The endpoint
with a rational root has only lower-degree irreducible factors. Its complete
cycle keeps every factor's original quotient field, exact local length and
both original coordinate maps. `AdjoinRootFactorLength` proves that length is
the factor's multiplicity; no reduced quotient replaces a repeated fiber.
The Milnor recurrence comes from actual K₃ rational reciprocity and the same
literal factor multiset. No norm-compatibility assumption is supplied.

`WeightTwoPointPresentation` presents each actual finite torus point using the
primitive element of its entire joint coordinate field. Its degree is the full
support degree. Thus `WeightTwoMilnorSurjective` proves surjectivity of the
original raw and derived integral Milnor symbol maps, the finite maps, and the
maps from K₂ modulo n, for every natural n. Signed sums and colliding point
images keep their original multiplicities.

The explicit cycle preimage is not yet proved to annihilate arbitrary singular
boundaries. Injectivity, a Milnor K₂–H²² isomorphism and its inverse remain open.
The new libraries and actual-group consumers pass the same strict Lean checks
and rejecting standard-axiom tests; they are included in the public root and
integration consumer.


## First-coordinate cycle evaluation and whole fibers

`WeightTwoCoordinateEvaluation` defines a candidate inverse on the original
signed finite-point cycles. It uses the minimal polynomial of the first
coordinate and the ordinary unit norm from the entire point field to that
coordinate field. `value_map_degree` proves the actual finite-extension degree
law. Identity-coordinate supports vanish, and rational graphs have their
original Milnor symbol value.

`WeightTwoCoordinateCycleEvaluation` identifies this evaluation with actual
finite-point pushforwards, retaining the image residue degree when the two
coordinates generate a proper subfield. It handles arbitrary signed sums,
collisions, and identity supports. The whole-fiber formulas retain every
maximal quotient and its local self-length, including nonreduced and empty
fibers. They give endpoint conservation for a finite flat family whose first
coordinate is fixed.

`PolynomialNormRootRecurrence` proves the exact root-symbol reciprocity
relation, including its repeated-entry sign term, and a lower-degree criterion
with explicit premises. General norm compatibility with DVR specialization,
arbitrary-curve boundary vanishing, and injectivity are still open. The
constant-first-coordinate theorem alone does not provide that descent.

`Motivic/Aglib/AlgebraicGeometry/FiniteCurveNormalization` constructs the
actual normalization of a finite faithful domain algebra over the original
k[t] in characteristic zero. Finiteness, the Dedekind property and generic
residue degree one are proved. Its pushforward preserves the entire actual
endpoint fundamental cycle, including singular targets, all branches and
nonreduced Cartier multiplicities. No finiteness of a different coordinate
projection is assumed.


## Local norm prerequisites

`HenselianPrincipalRoots` proves roots of actual principal units for every
positive invertible exponent, with residue-characteristic-zero consumers.
`RamifiedRestriction` derives the original K₂ tame and specialization
restriction formulas from the actual uniformizer equation; the specialization
correction and sign two-torsion are retained.

`PolynomialNormRestrictionKernel` shows that the actual finite separable
extension degree kills the restriction kernel, using one auxiliary polynomial
presentation. `PolynomialNormSplit` rewrites restriction of a polynomial norm
over a splitting field as the sum of all literal branch embeddings. These
results do not presume canonical norm independence or a Milnor norm tower.


## Principal-unit norms over complete DVRs

`CompleteDVRExtension` proves that the actual integral closure in a finite
separable extension of a complete DVR fraction field is a complete henselian
DVR, with finite residue extension and positive ramification. Literal field
embeddings induce the corresponding local integral-closure maps.

`PolynomialNormPrincipalUnit.polynomialNorm_principal_unit_completeDVR`
proves that both tame residue and specialization of the original polynomial
norm of {b,h} vanish when h is a principal unit in that actual integral
closure. The first entry b may have a zero or pole. The base residue field
has characteristic zero. The splitting field, all branch maps and the fixed
ramification/residue-degree annihilator are constructed, and Hensel roots in
the same integral closure remove that annihilator.

These source and consumer pairs pass strict Lean and rejecting standard-axiom
checks. General norm/tame compatibility, descent from noncomplete DVRs, and
arbitrary singular-boundary vanishing remain open.

`Motivic.Aglib.RingTheory.DVRNormValuation.order_norm` is a separately
importable, strictly checked general algebra result: the integer order of an
ordinary field norm is the actual residue-field degree times the source order,
including poles. Its perfect-base-field and finite integral-closure hypotheses
are explicit. It is not yet imported by the aggregate root; its focused
consumer includes the literal Milnor-order adapter.

## All-degree Milnor residues and rational exactness

`Motivic.KTheory.MilnorK` now exposes the actual integral quotient in every
nonnegative degree, its field maps and concatenation product, and canonical
DVR residues with the uniformizer in the final slot. Specialization changes
by the proved residue correction; the tame residue itself is independent of
the uniformizer. Repeated entries retain their minus-one factors, including
characteristic two and symbols with poles.

The actual polynomial-place residues have finite support on every class.
Canonical reduced representatives, coordinatewise degree generation and the
actual positive degree-stage equivalences prove the rational-function short
exact sequence in every positive Milnor degree over an arbitrary field.
The initial constant-field map has an actual specialization left inverse,
and the quotient by its image is the dependent finite sum of the original
residue-field Milnor groups. Residue degree zero is included. The left
projection formula uses a genuine field map into the valuation ring, and
allows an arbitrary right-hand Milnor class with poles.

`DiagonalWeightZero` computes the originally defined H^{0,0} as the integers.
The diagonal forward Milnor symbol, the actual top-degree H0 comparison, and
geometric corestriction and tower laws are available in every weight. The
full general Milnor-to-motivic isomorphism still needs presentation-independent
finite-extension norms, curve reciprocity and boundary-descent steps. Rational exactness alone does not
supply those steps.

These public endpoints and their focused consumers pass the strict compiler
and rejecting standard-axiom checks. The all-degree residue/exactness cohort
is included in the public root and the pinned-Lake integration consumer.
Strict A1-invariance is a parallel implementation in progress: newly added
A1 projection, transfer-exactness and relative-curve leaves must be read with
the snapshot's point-in-time status. The strict theorem is not yet proved.


## Strict A1-invariance: first concrete interfaces

`Cohomology/A1` uses the literal polynomial spectrum, projection, zero and one
sections, and graph precomposition. Homotopy invariance implies equality of
the actions of the two endpoints of an actual signed correspondence homotopy.
The all-degree strict-invariance predicate uses ordinary Ext cohomology with
the correct coefficient universe. Its comparison with the existing
single-complex cohomology commutes with actual restrictions and coefficient
maps; where universe parameters agree it is naturally isomorphic to Mathlib
ordinary sheaf cohomology. The full strict-invariance theorem is still open.

The actual category of Nisnevich sheaves with transfers is abelian, and its
underlying ordinary-sheaf functor preserves and reflects exactness. Kernel and
cokernel comparisons respect their actual structure maps. Actual degree-zero ordinary cohomology now carries its signed transfer action,
with graph restriction and coefficient naturality agreeing with ordinary H0.
Higher-cohomology transfers and ordinary-cohomology acyclicity are separate
remaining steps.

A finite-flat span now produces a finite correspondence for disconnected
smooth sources, retaining every generic length and residue degree. Proper,
flat Cartier subschemes of smooth relative curves are proved finite and
finitely presented, with finite locally free direct-image structure module.
Boundary avoidance gives the actual correspondence from the unchanged whole
divisor. Standard-triple splitting and the geometric A1 homotopies are still
being constructed.

`MilnorK/PolynomialNorm` additionally defines all-degree norms for each actual
monic irreducible polynomial presentation by rational residues and minus the
infinity residue. Rational-lift independence, finite rational reciprocity,
the positive degree formula and the left projection formula hold over every
field. Independence of the polynomial presentation and abstract extension
tower laws are not asserted by this construction.


## Actual contraction and norm compatibility

`PresheavesWithTransfers/Contraction` is the genuine cokernel of restriction
from the affine-line cylinder to its Laurent principal open. The signed
transfer action uses the actual exterior correspondences, and sections are
the ordinary quotient by that restriction's image. For HI coefficients the
canonical comparison is the kernel of restriction along the literal unit
section. Both maps, their split identity and coefficient naturality are
proved; the inverse is inclusion followed by the actual quotient.
The actual factor-exchange isomorphism now proves that parameter sections
preserve HI. Descending the genuine zero-section inverse through the epi
quotient proves contraction itself preserves HI. Comparison with Nisnevich
sheafification remains a separate open step.

The all-degree polynomial norm at degree two now agrees on every class with
the original norm under the proved presentation equivalence. This uses all
finite residues, infinity and actual residue-map surjectivity, with no
characteristic restriction. Its comparison with the original raw, derived
and finite H22 corestrictions retains characteristic zero and the existing
derived-category hypotheses. General norm presentation independence remains
open.


## Injective transfer sheaves and finite-support geometry

Lifted additive representables give an actual separator, while the additive
functor inclusion supplies exact filtered colimits. The left-exact Nisnevich
reflection therefore makes the actual transfer-sheaf category Grothendieck
abelian and gives actual injective embeddings. This does not yet prove that
their underlying ordinary sheaves are cohomologically acyclic.

Every line bundle on a semilocal affine scheme now has an actual unit
trivialization. Consequently every line bundle on the full scheme-theoretic
fiber of a finite morphism is trivial, including nilpotents and disconnected
fibers. The neighborhood spreading result below retains an actual finite
support hypothesis. These statements do not apply to an arbitrary entire
proper curve fiber: O(1) on P1 is not trivial.

All-degree Milnor residues additionally commute with actual unramified DVR
restriction, using a genuine local ring map and commuting fraction-field
map whose image of a uniformizer stays irreducible. Valuation/unit-part
compatibility is derived, not assumed at the public endpoint. This is not
a norm-residue theorem for general ramified extensions.


### Finite-support neighborhoods and the H0 base case

Finite prime avoidance and finite-presentation basis descent now spread a line
bundle trivialization to an actual principal open around any finite prime-point
set of an affine scheme, including nonclosed points and empty sets. For a
finite support map B → Y and a separate map B → X into an affine ambient X,
closed-image shrinking gives an open neighborhood of the chosen base point
whose whole support lies in the trivializing open. This concerns finite
boundary/support schemes; it does not trivialize every line bundle on a whole
proper curve fiber.

Actual ordinary H0 restriction is conjugate to restriction of sections through
the canonical zeroSections equivalence, in the original coefficient universe.
Thus HI coefficients give the degree-zero case of strict invariance; the inverse
is the literal zero-section restriction and is natural in objects and
coefficients. Positive cohomological degrees remain open.

### All-degree polynomial norm base change

Coefficient restriction of a characteristic-zero polynomial-presentation norm
is the sum over all actual monic irreducible target factors, for arbitrary
classes and all degrees including zero. At places with zero contraction every
restricted rational unit has an actual local-unit representative, giving the
necessary vanishing and full support bound. Infinity and total-residue norm
naturality hold in every characteristic. Primitive-element-independent finite
extension norms, towers, curve reciprocity and the full diagonal comparison
isomorphism remain separate work.


### HI sheaf contraction and ordinary point acyclicity

The literal parameter-product functor preserves the Nisnevich sheaf condition.
Consequently contraction of an already HI Nisnevich sheaf with transfers is
again an actual Nisnevich HI sheaf, with its original quotient and signed
transfers. This does not yet compare contraction and sheafification for a
general HI presheaf.

For one actual site point, the ordinary skyscraper functor is exact on abelian
groups. Its adjunction identifies ordinary cohomology with Ext from the
projective fiber of the existing free section-representing sheaf. Thus every
positive cohomology class of this skyscraper vanishes, naturally for the actual
restriction and coefficient maps. Actual smooth-site Nisnevich points over an
affine base are constructed from pointed etale neighborhoods of Spec kappa(x),
with actual common refinements, equalizers, cover lifting and fiber colimits.
The transfer-compatible closed-point acyclic envelope remains a separate
construction.

### Actual endpoint and norm comparisons

For finite-flat affine-line families whose joint parameter-target map is a
closed immersion, graph evaluation equals the span of the whole canonical
scheme-theoretic fiber. The proper flat Cartier adapter supplies finiteness,
and retaining the ambient open as a closed target supplies the joint embedding.
Tests retain two double components, an actual nonzero nilpotent and a nontrivial
idempotent. General relative-base and arbitrary nonembedding-target extensions
remain separate work.

The all-degree split norm formula identifies degree-one polynomial norms with
the ordinary determinant field norm in characteristic zero, on every class.
It also proves genuine degree-one presentation independence and the all-degree
mixed-product formula. Higher-degree presentation independence is not inferred
from the split formula alone; the prime-normal result below uses additional finite descent. A separate polynomial-stage proof establishes actual
mixed-symbol generation under an explicit degree-gap hypothesis, including
linear and quadratic extensions, characteristic two and finite signed
expansions. No prime-special extension is assumed to exist.

For every finite separable extension, in arbitrary characteristic and every
Milnor degree, a chosen primitive element gives an auxiliary degree retraction.
Therefore restriction kernels are killed by the extension degree, prime-to-p
restriction detects p-power torsion, and unrelated coprime-degree extensions
jointly detect classes. This auxiliary map is not asserted to be a canonical
finite-extension norm.

### Relative Ext and point-local correspondence lifts

The actual free abelian sheaf functor preserves monomorphisms. A smooth open
immersion therefore gives its genuine cokernel relative source and the
six-term Ext sequence, whose ordinary arrows are the original restriction
maps. Both the extension-class convention and the standard signed connecting
map are explicit. These are relative Ext groups of the pair; their
identification with closed-support cohomology or purity remains separate.

Finite support can now be lifted inside the actual Nisnevich-neighborhood
index of a chosen point, retaining every scheme-theoretic clopen piece and
its target label. For a correspondence generator this gives a finite sum of
literal incidence-Tor correspondence lifts. The hypothesis concerns only the
chosen finite support fiber, not a global covering family of the target.
The transfer-compatible action on germ classes and its representative
independence remain to be assembled.

Arbitrary graph postcomposition also preserves direct whole finite-flat
spans, even when the ambient target map is not finite and components collide.
Consequently the affine-line Cartier endpoint formula now applies to an
arbitrary target for a separated quasi-compact relative curve, retaining
explicit properness and flatness of its divisor. Relative-X specialization
requires a further actual graph-block Tor comparison; component-flatness
over X times the affine line is not assumed.

### Finite descent of Milnor relations

An actual defining relation over an algebraic extension descends to a finite
intermediate field. The original quotient's vanishing and equality therefore
have finite witnesses, with no separability hypothesis. When the extension
is separable and its finite intermediate degrees satisfy the displayed
coprimality condition, the existing degree retraction detects the corresponding
torsion. This does not construct a special closure or a canonical higher norm.

### Contraction and the actual relative degree-one group

`Cohomology.A1.ContractionRelative` maps the original contraction quotient
injectively into the relative degree-one Ext group of the literal Laurent
open in the affine-line cylinder. On an original Laurent section its value
is the negative genuine connecting extension class. Its image is exactly the
kernel of the relative-to-ordinary map. The coefficient and Ext universes
remain independent; no HI premise or purity identification is used.

Point-local signed Čech kernel relations now retain a common actual closed
finite support and ask for lifts only over the chosen source fiber. For a
closed source point, only its actual closed target centers enter. These
relations do not by themselves define an action on germ classes: the
pointed-neighborhood branches and representative independence must also be
controlled.

### Finite splitting witnesses for mixed symbols

For each actual Milnor class over a specified monic irreducible polynomial,
`MilnorK.SplitPolynomialGeneration` extracts a finite set of nonzero reduced
coordinate polynomials before choosing any future coefficient extension.
When these particular polynomials split, the class on every actual irreducible
factor has a finite signed mixed-symbol expansion. The proof retains the
factor map and its divisibility and works in arbitrary characteristic.

The Mathlib-only candidate `Aglib.FieldTheory.SylowFixedField` proves that a
finite Galois field containing the roots of a specified family of polynomials
of degree below a prime has a prime-to-that-prime intermediate field in which
that family still splits. This is a finite-family statement, not a global
special-field construction. The finite-class application now preserves the original prime-degree root
field and proves comparison after a genuine coprime-degree restriction, as
described below. General norm and boundary compatibilities remain separate.


### Prime-normal presentation independence

The actual polynomial-presentation norm is now invariant under a specified
base-field algebra equivalence when the original extension has prime degree
and is normal, in characteristic zero and every Milnor degree. The proof
compares the actual embedding sums over a common splitting field, then uses
two genuine finite restrictions of coprime degrees. The second restriction
comes from finite classwise mixed generation; it is not a presumed global
special closure. Degree zero has its own integer degree-law proof. Arbitrary
finite-extension independence, norm towers and the full diagonal Milnor
isomorphism remain open.

### Actual germ locality, cohomology evaluation and local endpoint Tor

Existing sections with identical germs at the finitely relevant target
centers have the same source germ after an arbitrary signed correspondence.
The proof keeps the original finite support and signed lift factorization.
An action on arbitrary tuples of germs still requires control of the chosen
lift supports and independence of the chosen lift. For a fixed lift whose
actual support fibers map to designated target centers, representative
independence is now proved at arbitrary source points. The transfer-compatible
acyclic envelope must use all scheme points, as corrected in the official
MVW erratum to Exercise 12.10. The point-preserving finite-support construction
now gives actual branch-controlled correspondence lifts for arbitrary chosen
target neighborhoods, even when target centers specialize to each other.
Combining this with fixed-lift locality proves independence of section
representatives. Existing sections now have signed finite-support locality at
arbitrary source points, including nonclosed points and empty fibers. The
original Čech pairing and local contraction also retain actual incidence and
common-support point witnesses through every signed sum. Independence of
different lift choices and the complete all-point envelope remain in progress.

Ordinary positive-degree Nisnevich cohomology vanishes at the actual base
field object for arbitrary coefficient sheaves. A separate theorem covers
henselian local spectra equipped with an explicit smooth, separated,
quasi-compact structure map, hence actual objects of the smooth site. These
theorems do not identify arbitrary henselizations with smooth objects or prove
positive-degree cohomology vanishing on the affine line.
Every ordinary positive-degree cohomology class is also proved to vanish
after restriction along an actual smooth Nisnevich covering family. This
uses ordinary injective dimension shifting and the actual cokernel-section
image sieve, without assuming acyclicity of injectives with transfers. The
ordinary H¹ descent interface now constructs actual local quotient lifts and
proves that a literal coefficient coboundary kills the original extension-class
boundary. A direct square criterion uses the actual two-arrow restriction difference
and genuine sheaf gluing to kill the same H¹ class; its geometric splitting
input remains explicit. The distinguished-square geometry needed to apply
this criterion on the affine line is still under construction.

The original contraction-to-relative-degree-one map now commutes with actual
restriction and coefficient maps. The local graph-plus-parameter-cut Tor is
identified in all degrees with the one-equation Koszul complex on the actual
support stalk. The component result uses regularity inherited from the whole
flat family, without asserting component flatness. A nonreduced family over
a disconnected relative base is an explicit consumer. The literal four-factor
incidence Tor for each original integral component is now identified with
the actual endpoint fundamental correspondence, including its finite
pushforward. The whole finite-flat relative family's endpoint cycle is also
proved to be the sum of its original component fibers weighted by their
generic local lengths. Both literal fiber models are covered, including a
proved nonreduced family over a disconnected source. Assembly with every
source graph component now gives the actual categorical endpoint formula for
the whole family. A genuine proper-flat relative Cartier divisor supplies the
retained closed embedding; forgetting the retained coordinate allows an
arbitrary target map, including a tested nonfinite map. Strict A¹-invariance
in positive degrees remains open.

### Ramified residue and ordinary unit norms

The actual all-degree Milnor residue commutes with ramified restriction with
the explicit ramification factor. For finite DVR extensions, the ordinary
norm of an integral unit reduces to the residue-field norm raised to that
factor. The latter is a reusable algebraic statement over arbitrary
characteristics; its proof retains the full nonreduced closed fiber and its
length. The selected polynomial-presentation Milnor norm has corresponding
ring-unit compatibility under the stated characteristic-zero hypotheses.
A native Henselian normalization lemma lifts an actual residue unit to a
base unit and removes the remaining principal unit by a root with residue
one, under explicit invertibility of the exponent. Native DVR lemmas now give
the exact normalized ordinary norm of an extension uniformizer in prime field
degree, including its determinant sign. They derive the actual degree = e f
formula and use an Eisenstein binomial in the residue-degree-one branch. The
all-degree Milnor norm–residue square is proved for an arbitrary base-field
prefix class and arbitrary final extension-field unit, including poles, in
prime degree with explicit residue presentation and characteristic-zero residue
hypotheses. A direct consumer constructs the genuine complete-DVR integral
closure. General canonical norm independence and the full diagonal Milnor
isomorphism remain unfinished.


## Historical source snapshot: 16 October 2026

Captured 2026-10-16T19:18:48.532440+00:00 UTC.

This is the complete current source tree with pinned Lake dependencies,
licenses, build scripts and direct consumers. That original October 16 snapshot contained no compiler caches,
validation logs or historical evidence archives. This October 17 recovery
package includes the selected fresh success logs in checkpoint-evidence.

The checked public root and actual native Lake integration now include:

- The categorical endpoint identity for whole finite-flat relative families,
  assembled from their original integral components and generic lengths.
  Genuine proper-flat relative Cartier divisors supply the retained closed
  embedding. The target can then be forgotten through an arbitrary map.
  Direct consumers retain nonreduced fibers, a disconnected two-line source,
  and a proved nonfinite forgetting map.
- Signed finite-support germ locality at arbitrary scheme points, including
  nonclosed source points and empty fibers. The original Čech pairing and
  contraction retain literal incidence/common-support point witnesses. A
  controlled point-local boundary now preserves the chosen target-fiber
  properties on both sides; it does not yet construct the complete all-point
  acyclic transfer envelope or prove independence of all lift choices.
- Ordinary H¹ descent from actual local quotient lifts and coefficient
  coboundaries. A direct square criterion kills the original extension-class
  boundary using actual sheaf gluing and the literal A-minus-Y restriction
  difference. The geometric splitting needed for affine-line vanishing is
  still an explicit, unfinished input.
- In prime field degree, the exact ordinary uniformizer norm coefficient,
  including its determinant sign, derived from actual DVR ramification and
  residue degrees. The selected polynomial-presentation Milnor norm satisfies
  the all-degree norm–residue square for an arbitrary base-field prefix class
  and arbitrary final extension-field unit, including negative-order poles.
  The residue presentation, Henselian/exponent-invertibility and characteristic-
  zero residue hypotheses are explicit. Direct consumers include K₀ prefixes,
  the original K₂ tame map and a genuine complete-DVR integral closure.

The public root, its integrated direct consumer, and a real `lake env lean`
check of `Tests/MotivicIntegration.lean` all succeeded at this checkpoint.
Separate native Milnor consumers also succeeded with standard-axiom checks.
Checks use the original two-compiler guard, `-j1`, 200000 heartbeats and the
pinned official cache; no clean rebuild or new axiom was used.

Additional current working leaves are preserved, with these capture statuses:

- `CategoryTheory/Sites/DistinguishedSquare` has a successful strict check for
  the generic diagonal/overlap-cover sheaf pullback theorem. The new geometric
  `AlgebraicGeometry/NisnevichDistinguishedSquare` is under its first check;
  the actual smooth-site adapter is not yet complete.
- `RingTheory/PrescribedTrivialization` is a source draft awaiting its first
  elaboration and exact pinned dependency cache. The scheme-level extension
  of a specified boundary trivialization remains unfinished.
- `Cohomology/A1/SquareDifferenceActions` and its direct consumer are present.
  Its source has one known endpoint-identity elaboration error and is pending
  repair; this leaf is not included in the checked public root.
- `Transfers/ControlledCechGermComparison` has a successful library check;
  its direct consumer is not yet written and the full envelope is not claimed.

The next strict-A¹ field step follows only the needed rightmost MVW 21.9
splitting, followed by actual distinguished-square H¹ descent. It does not
require constructing an entire Čech contraction. The complete positive-degree
strict A¹ theorem remains open. General canonical Milnor norm independence,
all-class norm compatibility, curve boundary descent and the full diagonal
Milnor isomorphism also remain open. No cancellation theorem is claimed.

