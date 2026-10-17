# Local Aglib candidates

This directory holds general algebraic geometry and its reusable algebraic
foundations developed in this project, organized for possible contribution to
Aglib or Mathlib. These are local `Motivic.Aglib` modules; placement here does
not mean they have been accepted upstream or change the pinned dependencies.

The imported candidate tree has mixed dependencies: some leaves import back
into other Motivic families. Each promotion must lower those dependencies
before it can become a standalone upstream interface. Historical checked-source
coverage is recorded in [provenance](../../doc/provenance/README.md); the list
below describes inherited interfaces, not a new aggregate verification.

The inherited reusable modules include:

- `CategoryTheory/SheafifyAdditive.lean`: ordinary sheafification preserves
  source-arrow additivity on a site with a principal covering basis, with
  explicit sheafification and coefficient-universe assumptions.
- `RingTheory/HenselianEtaleSections.lean`: residue-compatible lifts for étale
  algebras over henselian local rings, including local Artinian bases.
- `RingTheory/ArtinianEtaleSections.lean`: simultaneous residue-compatible lifts
  for formally smooth and étale algebras over arbitrary Artinian rings.
- `AlgebraicGeometry/HenselianEtaleSections.lean`: residue-compatible sections
  for arbitrary étale schemes over henselian local or local Artinian bases.
- `AlgebraicGeometry/ArtinianEtaleSections.lean`: sections over a whole locally
  Artinian scheme from rational lifts at its points.
- `AlgebraicGeometry/Sites/NisnevichHenselian.lean`: split members and maximal
  covering sieves over henselian local spectra.
- `AlgebraicGeometry/Sites/NisnevichHenselianEvaluation.lean`: exact ordinary
  abelian-sheaf evaluation and sheafification-unit isomorphisms there.
- `AlgebraicGeometry/NisnevichQuasiFinite.lean`: pointed Nisnevich isolation
  of a quasi-finite branch, with its actual residue-field map and singleton fiber.
- `AlgebraicGeometry/NisnevichFiberSections.lean`: lifting entire locally
  quasi-finite fibers through a pointwise Nisnevich-surjective étale map.
- `AlgebraicGeometry/NisnevichFiniteSplitting.lean`: complete clopen splitting
  of a finite support on an actual pointed Nisnevich neighborhood.
- `AlgebraicGeometry/FiniteEtaleNeighborhoodIso.lean`: a finite étale singleton
  fiber with its actual residue-field isomorphism extends to a neighborhood
  isomorphism, via the existing rank function.
- `AlgebraicGeometry/NisnevichFiniteBranchLift.lean`: a residue-compatible
  separated étale lift extends over a Nisnevich neighborhood of a singleton
  finite fiber, retaining the complete pulled-back support.
- `AlgebraicGeometry/NisnevichFiniteLifting.lean`: simultaneous lifting of an
  entire arbitrary finite support through a separated étale map on an actual
  pointed Nisnevich neighborhood, including empty and nonreduced fibers.
- `AlgebraicGeometry/NisnevichFiniteFamilyLifting.lean`: a finite support lifts
  through an arbitrary separated étale family on a complete finite clopen
  partition after an actual pointed Nisnevich neighborhood. The family may be
  infinite or empty; repeated labels and nonreduced supports are retained.
- `AlgebraicGeometry/Cycles/FinitePushforwardInjective.lean`: pushforward along
  an actual closed immersion is injective on signed integral cycles, without
  reducedness or Noetherian assumptions.
- `AlgebraicGeometry/NisnevichFiniteSubfamily.lean`: a locally finite-type
  residue-field-lifting family over a Noetherian base has a finite subfamily
  retaining the actual residue-field isomorphisms, including nonreduced bases.
- `AlgebraicGeometry/FiniteCommonImage.lean`: finitely many closed supports
  finite over their source have a common actual closed image finite over it.
- `AlgebraicGeometry/ClosedImageBaseChange.lean`: the literal base-changed
  support embeds into the new ambient product by a Cartesian closed immersion,
  with no flatness assumption on the base change.
- `AlgebraicGeometry/ProductDiagonal.lean` and `ProductDiagonalBaseChange.lean`:
  actual Cartesian factorization of product diagonals, with stated flatness
  conditions for the remaining projection.
- `Algebra/Homology/KoszulTorRegularBlockReduction.lean`: eliminate a proved
  regular leading block from actual Tor, retaining the remaining Koszul complex.

- `CategoryTheory/SheafifyAdditive.lean`: a principal covering basis makes
  ordinary sheafification preserve addition of source-category arrows.
- `CategoryTheory/SheafifyLocallyBijective.lean`: a locally bijective map into
  a sheaf identifies it with ordinary sheafification through the canonical
  lift, retaining the actual unit equation.
- `CategoryTheory/CokernelAdditive.lean`: an epimorphic quotient of an additive
  functor is additive, in particular the actual ordinary functor cokernel.
- `AlgebraicGeometry/LaurentTorus.lean`: the actual Laurent spectrum is smooth,
  separated and finite type, with its literal evaluation-at-one closed section.
- `AlgebraicGeometry/SmoothSiteNisnevichEvaluation.lean`: smooth Nisnevich covers
  split at the base field, giving exact ordinary sheaf evaluation and an actual
  sheafification-unit isomorphism on base sections.

- `CategoryTheory/AdditiveFunctorLimits.lean`: a limit of additive functors is
  additive, using the actual joint monicity of its evaluated projections.
- `CategoryTheory/FullSubcategoryHomotopy.lean`: additivity of natural retracts
  and componentwise lifting of maps, actual homotopies and homotopy equivalences
  to a full subcategory; zero extension and signed shift preserve them.

Their import paths begin with `Motivic.Aglib`. Mathematical namespaces such as
`AlgebraicGeometry`, `Motivic.HenselianEtale`, and `Motivic.ArtinianEtale` are
preserved; local organization does not require theorem-name wrappers.

Keep motivic-specific constructions and consumers in their own project
families. Other general modules are moved separately with their affected
imports and consumers, without delaying the active mathematical proofs.

## Field-change and norm helpers

`RingTheory/FlatTorsionFreeMinimalPrimes` and
`AlgebraicGeometry/FlatBaseChangeGeneric` preserve generic components under
the stated actual flat/torsion-free maps. `SmoothSiteBaseChangeProducts`
compares literal relative products. `RingTheory/FiniteAlgebraNormLength`
computes actual determinant norms through prime filtrations and finite
localized lengths. Correspondence and motivic consumers remain downstream.

`RingTheory/PolynomialFiberNorm` proves norm base change and equality of the
actual local-length-weighted residue products in polynomial fibers.
`AlgebraicGeometry/SmoothSiteDiagonalBaseChange` gives the literal Cartesian
diagonal square, flat pair projection and transport of a specified regular
kernel list. `FlatFundamentalCycle` retains full component multiplicities in
field products, and `ClosedImmersionKoszulEuler` evaluates signed closed-cycle
equalities by a fixed local Koszul Euler functional with its Artinian cut.

`RingTheory/MonicUnitInterpolation` constructs a monic constant-unit polynomial
family, its finite free root algebra and actual endpoint fiber isomorphisms.
The norm/identity target includes repeated roots and arbitrary characteristic.

`AlgebraicGeometry/FiniteFlatCurveComponents` proves flatness of every reduced
component of a finite flat scheme over a field’s affine line, without assuming
the whole scheme reduced. `RingTheory/CartierCutLength` identifies a regular
singleton Koszul Euler characteristic with the actual finite quotient length,
including nonreduced local rings and explicit flat scalar transport.

`AlgebraicGeometry/ClosedSupportFlatRegularity` transports the literal affine-line
fiber parameter through an actual closed-support stalk quotient.
`AlgebraicGeometry/FiniteFlatCurveSpecialization` specializes the full fundamental
cycle of a finite flat curve family with its original component multiplicities.
The closed endpoint map is not required to be flat.
`RingTheory/AdjoinRootSimpleLocalization` proves the original quotient localization
has length one at a simple scalar root while retaining nilpotents at other branches.

`AlgebraicGeometry/FiniteSchemeNormBaseChange` identifies global sections of an
actual finite-scheme pullback with its literal scalar extension. The canonical
map respects both structural scalars and the original projection. Determinant
norms of sections and units commute with every field map, retaining the full
possibly nonreduced finite scheme.

- `RingTheory/TwoUnitPolynomialFamily.lean`: a monic positive-degree two-unit
  quotient, faithful flatness, root/complement-preserving scalar and whole
  tensor-fiber maps, and an explicit degree-three family with precisely the
  two necessary unit-value hypotheses. Includes nonreduced characteristic-
  three consumers; no geometric relation is asserted by this algebra API.

- `AlgebraicGeometry/FiniteFieldResidueDegree.lean`: identifies geometric
  residue degree of a field-spectrum map with the original scalar finrank,
  using the actual global-evaluation square, without separability assumptions.
- `RingTheory/DomainCartierMultiplicity.lean`: fixed-support Euler replacement
  at the unique generic prime of a local domain yields the actual generic
  length times Cartier-cut length. Module quotient length requires its own
  regularity, and Artinian support proves finiteness before integer conversion.
- `AlgebraicGeometry/GenericFinitePushforwardMultiplicity.lean`: the whole
  finite-algebra generic multiplicity at every target chart point equals the
  actual generic residue degree of a finite dominant integral scheme map.
- `AlgebraicGeometry/FlatFundamentalCycleTower.lean`: literal pullback identity
  and tower isomorphisms preserve whole fundamental cycles; the flat second
  pullback retains the full intermediate component lengths.

These modules reuse some general local-algebra and cycle prerequisites still
located elsewhere in `Motivic/`; upstream extraction also needs those imports.

- `AlgebraicGeometry/FiniteCurvePushforwardSpecialization.lean`: actual finite
  pushforward commutes with the Cartier endpoint cut for finite surjective
  maps of integral affine-line curves. The map between curves need not be
  flat and neither endpoint fiber is reduced; all original local lengths
  and residue degrees are retained.

- `RingTheory/AdjoinRootScalarBranches.lean` and
  `AlgebraicGeometry/AdjoinRootScalarBranches.lean`: literal irreducible-factor
  quotient fields, scalar-compatible branch maps, full tensor pullbacks, and
  fundamental-cycle decompositions. Squarefree length-one statements retain
  their reducedness proof; general endpoints keep all local lengths.
- `RingTheory/AdjoinRootFactorLength.lean`: the actual quotient localization is
  the quotient of the polynomial DVR by the original equation. Its self-length
  equals the factor multiplicity and normalized-factor count, in all characteristics.
- `RingTheory/AdjoinRootBalancedFractions.lean`: balanced numerator/denominator
  representatives in an irreducible root field, via an actual dimension-kernel
  argument; leading coefficient cancellation retains the even-degree boundary.
- `RingTheory/TwoUnitMonicDeformation.lean`: constant-degree monic deformations
  preserving two genuine units on the whole finite-free algebra, full tensor
  endpoint coordinates, and rational-root insertion with strict factor-degree descent.
- `AlgebraicGeometry/FiniteTwoUnitPolynomialFamily.lean`: retaining parameter
  and root gives a closed immersion into a separated ambient scheme, and exact
  full scheme-theoretic fiber identifications; no reducedness is assumed.
- `AlgebraicGeometry/FinitePointBaseChange.lean`: finite scalar pullbacks and
  whole fundamental-cycle pushforward with the original generic residue degree.

- `AlgebraicGeometry/FiniteCurveNormalization`: normalization of a finite faithful
  domain k[t]-algebra in characteristic zero, finite Dedekind closure and exact
  whole-fiber finite-pushforward preservation over the original parameter.
- `RingTheory/DVRCartierLength.lean`: the actual quotient by a specified nonzero
  DVR scalar has length equal to its normalized `IsDiscreteValuationRing.addVal`.
  The equality is in `ℕ∞` before integer conversion and includes repeated orders.
  This leaf uses only Mathlib imports and its native DVR namespace.
- `AlgebraicGeometry/FiniteCurveBranchOrders.lean`: every actual normalization
  endpoint stalk is proved to be a DVR, retaining the original `t - a` scalar.
  Its full endpoint coefficient is that scalar's finite normalized order; the
  original possibly singular curve's coefficient is the sum over all actual
  normalization branches of the original residue degree times that order.
  Neither original normality nor reduced fibers nor a single-branch assumption
  is required. This adapter still imports the existing Motivic finite-curve,
  normalization, and integral-cycle infrastructure; it is not a standalone
  Mathlib extraction. It establishes no Milnor norm, residue-symbol comparison,
  reciprocity, or boundary descent. The matching `MotivicTest/DVRCartierLength.lean`
  and `MotivicTest/FiniteCurveBranchOrders.lean` check literal endpoint scalars,
  repeated powers, actual residue maps, full branch sums, and standard axioms.

## Polynomial normality and going down

`RingTheory/MvPolynomial/IsIntegrallyClosed.lean` provides native
`MvPolynomial.isIntegrallyClosed_fin` with the original normal-domain
hypotheses. The [going-down family](RingTheory/Ideal/GoingDown/README.md)
provides compatible-equivalence transport, arbitrary quotient/surjection
descent for tensor products, polynomial going down and finite-type base change
of an integral faithful normal-base inclusion into a domain. These leaves use
Mathlib, focused pinned Aglib leaves and lower `Motivic.Aglib` candidates.
`RingTheory/Ideal/GoingDown/MinimalPrimes.lean` specializes upstream
minimal-prime contraction to the zero ideal, preserving arbitrary, possibly
nonreduced target algebras and independent ring universes. Smooth normality and actual
finite-scheme base-change applications remain downstream; no domain or
reducedness premise is imposed on the finite-type base-change algebra or its
tensor product.
