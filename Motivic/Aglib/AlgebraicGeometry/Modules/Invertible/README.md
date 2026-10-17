# Semilocal and finite-fibre line-bundle trivializations

`Semilocal.lean` uses the existing actual module-sheaf definition
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

`FiniteFiber.lean` transports these isomorphisms through the canonical affine
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

These theorems do not spread a fibre trivialization to an open neighborhood,
trivialize a line bundle on an arbitrary proper curve fibre, construct a
standard-triple splitting, or supply an A¹-homotopy. Finite-set localization
and descent to an open neighborhood, followed by closed-image base shrinking,
remain separate steps. In the relative-curve application, the finite scheme is
the boundary/support scheme; it is not the compactified positive-dimensional
curve itself. For example, the line bundle O(1) on the complete curve P¹
is not trivial.

## Actual dual twisted ideals and evaluation

`DualTwistedIdeal.lean` constructs the literal isomorphism
`I ⊗ dual(T) ≅ dual(T ⊗ dual(I))`, and its three-factor version, from
native evaluation, associativity, and symmetry. `TensorLineBundleSections.lean`
retains the original maps on pure tensors. `DualUnitFrame.lean` and
`RankOneReciprocity.lean` supply the actual local dual frame evaluation and
`d(x) • y = d(y) • x` on arbitrary open sections, without global triviality.
`DualTwistedIdealPairing.lean` computes the same global isomorphism in those
frames; `DualTwistedIdealPairingLaw.lean` proves its global pairing law by
sheaf separatedness. `DualTwistedIdealEvaluation.lean` specializes the pairing
to the original canonical divisor section, not a replacement section.
`DualTwistedIdealProduct.lean` combines these into unconditional original
section and three-factor product identities. Thus subsequent boundary
restriction retains the actual global line isomorphism and its evaluation.
