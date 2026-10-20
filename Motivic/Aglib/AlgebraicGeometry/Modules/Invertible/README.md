# Semilocal and finite-fibre line-bundle trivializations

`Frames/Semilocal.lean` uses the existing actual module-sheaf definition
`Scheme.Modules.Invertible.IsLocallyRankOne` and Mathlib's algebraic
Picard/semilocal basis theorems. Its results are:

- `tildeUnitIsoOfSubsingletonPic` turns trivial algebraic Picard group into an
  actual unit isomorphism for the associated sheaf of an invertible module.
  Mathlib supplies its semilocal instance; no Picard triviality proof is duplicated.
- `finiteLocallyFree_of_isLocallyRankOne` keeps the original singleton local bases.
- `finrank_baseChange_globalSections_eq_one` computes the rank of the actual
  scalar extension of affine global sections over every field-valued point.
  It uses the canonical tilde counit and actual geometric pullback comparison.
- `semilocalLineBundle_trivial` constructs a genuine sheaf/unit isomorphism
  for every line bundle on the spectrum of a semilocal ring. The original
  global sections are finite projective, and their maximal residue tensors
  have dimension one, so Mathlib's existing semilocal basis theorem applies.

`Frames/FiniteFiber.lean` transports these isomorphisms through the canonical affine
comparison. `finiteAffineLineBundle_trivial` applies to an affine scheme with
finitely many topological points. `finiteFiberLineBundle_trivial` therefore
trivializes any line bundle on the entire actual scheme-theoretic fibre of a
finite morphism. Empty and nonreduced fibres are included; there is no flatness,
Noetherianity, perfect-field, infinitude, or rational-point premise.

The algebraic source is [Stacks Project, Tag 02M9](https://stacks.math.columbia.edu/tag/02M9),
whose constant-rank semilocal freeness theorem is already implemented in
Mathlib. The affine and field-fibre comparisons come from pinned Aglib.
The source statement and its comment about Mathlib's finite-flat strengthening
were reviewed on 2026-10-16.

These theorems do not spread a fibre trivialization to an open neighborhood
or trivialize a line bundle on an arbitrary proper curve fibre. Finite-set localization
and descent to an open neighborhood, followed by closed-image base shrinking,
remain separate steps. In the relative-curve application, the finite scheme is
the boundary/support scheme; it is not the compactified positive-dimensional
curve itself. For example, the line bundle O(1) on the complete curve P¹
is not trivial.

## Actual dual twisted ideals and evaluation

`DualTensor/Basic.lean` constructs the literal isomorphism
`I ⊗ dual(T) ≅ dual(T ⊗ dual(I))`, and its three-factor version, from
native evaluation, associativity, and symmetry. `Sections/TensorLineBundleSections.lean`
retains the original maps on pure tensors. `Frames/DualUnit.lean` and
`Sections/RankOneReciprocity.lean` supply the actual local dual frame evaluation and
`d(x) • y = d(y) • x` on arbitrary open sections, without global triviality.
`DualTensor/Pairing.lean` computes the same global isomorphism in those
frames; `DualTensor/PairingLaw.lean` proves its global pairing law by
sheaf separatedness. `DualTensor/Evaluation.lean` specializes the pairing
to the original canonical divisor section, not a replacement section.
`DualTensor/Product.lean` combines these into unconditional original
section and three-factor product identities. Thus subsequent boundary
restriction retains the actual global line isomorphism and its evaluation.

## Boundary-framed data

[BoundaryFramed](BoundaryFramed/Basic.lean) and [BoundaryFramedTensor](BoundaryFramed/Tensor.lean)
retain actual line bundles, boundary trivializations and their tensor maps.
The [divisor-pair consumer](../../RelativeCurve/Sections/DivisorPairs/BoundaryFramed.lean)
uses this concrete framing. General relative-Picard comparison, H0 and norm
constructions remain outside this interface.

## Prescribed frames and whole zero support

| Exact import | Interface and retained boundary |
| --- | --- |
| `Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.FiniteFreePrincipal` | A produced frame on the literal finite-free principal base change around the chosen target point. |
| `Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.SupportRegularity` | Global monicity from monicity on an open containing the entire original zero support. |
| `Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.UnitOpen` | The actual unit domain of the original functional and factorization of maps on which its pullback is invertible. |
| `Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.Prescribed.FunctionalCoordinate` | Exact ideal-functional coordinates in the same prescribed affine frame extension. |
| `Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Boundary.RationalUnitGluing` | Gluing original representatives of one rational germ on their unchanged union, with actual boundary values. |

The finite-source frame interface does not impose source-domain or reducedness
hypotheses. The zero-support regularity bridge uses the original chart
coefficient's unit opens; finite flatness of a zero scheme alone is not a
regularity proof. Prescribed coordinates keep the ideal-functional direction,
not a substituted dual-line coordinate.

Rational-unit gluing retains the caller's original local unit/germ equations,
boundary equations and coverage. The boundary source may be nonreduced; its
value-one equation is equality of actual sections, not residue values.

## Literal functional quotients on affine charts

[FunctionalQuotientAffineChart](FunctionalQuotientAffineChart.lean) works in
`AlgebraicGeometry.Scheme.Modules.Invertible`, for schemes in universe `u`
and the caller's actual module functionals `a,c : M ⟶ 𝟙`.
`functionalQuotient_pullback` identifies the pullback of `c⁻¹ ≫ a` with
the quotient of the composite pullbacks, retaining denominator-invertibility
on the two displayed maps. `functionalQuotient_comp` compares nested and
composite pullbacks when the denominator is invertible on the composite.
`pullbackUnitMap_comp_isIso_of_nested` needs invertibility only on the nested
chart; it does not infer a unit on the intermediate parameter scheme.

For an affine open `U`, `functionalQuotient_fromSpec_coefficient` identifies
the coefficient on `U` transported by `U.topIso` with the coefficient on its
canonical `Spec Γ(X,U)` chart transported by `ΓSpecIso`. The parameter version
`functionalQuotient_parameter_fromSpec_coefficient` retains a prior actual
parameter map and both displayed composite denominator-unit hypotheses.
The canonical pullback-composition maps appear in these equations; a dual
of a newly chosen pulled section is not substituted for the original
functional. Generic-fiber isomorphism comparisons and the
[R3/R5 constructors](../../RelativeCurve/Pencils/README.md) consume these identities.

## Marked frames after two fixed coefficient localizations

[Frames/RelativeCurve/TwoLocalizationMarked](Frames/RelativeCurve/TwoLocalizationMarked.lean)
uses `AlgebraicGeometry.RelativeProjectiveLine.TwoLocalizations` and its
[literal source, retained curve and marked-product maps](../../ProjectiveLine/BaseChange/README.md).
For a commutative `R : Type u`, fixed `r : R` and `s : Localization.Away r`,
a finite projective-line map `F`, an open retained inclusion `j` and a marked
map `z`, `markedIdealFrame` transports the supplied original marked ideal frame.
`markedIdealFrame_coordinate` retains its exact scalar on the whole marked
scheme. Neither localization element is required to be nonzero.

`markedDivisorFrame` additionally requires relative smooth dimension one on
the original retained curve. It dualizes the final original graph-ideal line
to split the positive divisor line. Given the original disjoint boundary map,
`exists_fullBoundaryDivisorFrame` glues this same marked frame with the canonical
infinity frame and retains both coproduct equations. The original frame remains
an explicit input; this interface supplies no global Picard comparison.
