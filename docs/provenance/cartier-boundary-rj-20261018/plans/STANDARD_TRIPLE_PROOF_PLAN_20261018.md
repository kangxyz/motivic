# Standard triples and distinguished-square nullhomotopies

Research and proof plan, 2026-10-18. The research plan was delivered and scoped implementation is in progress.
This is an independent upstream lane, not a completion certificate and not a prerequisite for continuing the existing narrower strict-A1 boundary-Epi implementation.

## 1. Verified reference and target

Primary reference: Mazza–Voevodsky–Weibel, *Lecture Notes on Motivic Cohomology*, published Clay edition:
https://www.claymath.org/wp-content/uploads/2022/03/Motivic-Cohomology.pdf

Controlling locations: Definitions 11.5 and 11.11; Proposition 11.15; Definitions 21.1 and 21.5; Theorem 21.6; Lemmas 21.3 and 21.7–21.10; Corollary 21.11. Printed pages 177 and 181 were visually inspected from the local copy (PDF pages 192 and 196, one-based). The prime marks, map directions, two differential signs, and final contracting maps agree with the formulas below. The author-maintained errata at https://sites.math.rutgers.edu/~weibel/Books/MVW.errors.pdf was read on 2026-10-18; it currently has no correction to Lectures 11 or 21. Absence of an erratum is not a proof.

The final theorem is the actual map of complexes

    F(MV(Q)) → F(MV(Q'))

being nullhomotopic for each HI presheaf with transfers F. Required geometric hypotheses are:

1. Q is induced by a covering morphism of standard triples over a smooth base S.
2. r: Q' → Q is a morphism of upper distinguished squares.
3. rX: X' → X is an open immersion and the target standard triple is split over this specified X'.
4. X' and Y' are affine.

No Nisnevich-sheaf hypothesis on F, perfectness, infinitude of the field, higher-cohomology invariance, or strict-A1 consequence is included in the published target. The coefficient universe should remain arbitrary as in the native presheaf interface.

Only the identity specialization under these same hypotheses gives a split-exact complex. An arbitrary distinguished square is NOT claimed to be split exact.

A standard triple consists of a proper relative curve compactification, normal compact total scheme, smooth base, quasi-affine smooth retained curve, and disjoint closed infinity and marked loci whose union lies in an affine open of the compactification. Its splitting is a trivialization of the diagonal divisor line restricted to X' ×_S Z. The repository represents the diagonal by its actual ideal; passing to its dual must be explicit.

A covering morphism is finite on compactifications, preserves the retained opens, is etale on those opens, and identifies the marked closed fibers by an isomorphism. Its restriction Y → X need not be finite. Do not replace that assumption by global finiteness of Y → X.

The statement does not separately assume that rY is open or that Q' is the literal restriction of Q. The implementation must handle the stated square morphism, or clearly label any first restricted theorem as narrower.

## 2. Exact signs and simultaneous witness

Use forward composition, with graph symbols suppressed only in this section:

    u: B → Y,    g: B → A,    f: Y → X,    i: A → X,
    u ≫ f = g ≫ i.

Prime symbols denote Q'. The components of r are rX, rY, rA, rB.
Construct ONE simultaneous triple of actual finite correspondences

    λA: X' → A,    λB: Y' → B,    ψ: A' → B.

The following six equations must hold in the actual A1-homotopy relation (or via explicit cylinder witnesses; a finite additive combination of elementary witnesses also suffices):

    E1  λA ≫ Γ(i)                         ~ Γ(rX)
    E2  λB ≫ Γ(u)                         ~ Γ(rY)
    E3  λB ≫ Γ(g)                         ~ Γ(f') ≫ λA
    E4  ψ ≫ Γ(u)                          ~ 0
    E5  Γ(i') ≫ λA - ψ ≫ Γ(g)            ~ Γ(rA)
    E6  Γ(u') ≫ λB - Γ(g') ≫ ψ           ~ Γ(rB).

Independent existential choices for these equations are insufficient. In particular E3 and E5 are not consequences of choosing unrelated left and right pencils.

Put C0=F(X), C1=F(A)⊕F(Y), C2=F(B), and use the original maps

    d0(x)   = (i* x, f* x),
    d1(a,y) = -g* a + u* y.

The contravariant chain map has components rX*, (rA*,rY*), rB*. Define

    s1(a,y) = λA* a,
    s2(b)   = (ψ* b, λB* b).

Its identities are j0=s1 d0, j1=d0' s1+s2 d1, j2=d1' s2.
They have respectively 1, 4, and 1 matrix entries. For j1 the entries are

    (A,A): i'* λA* - ψ* g* = rA*        [E5]
    (A,Y): ψ* u* = 0                    [E4]
    (Y,A): f'* λA* - λB* g* = 0         [E3]
    (Y,Y): λB* u* = rY*.                [E2]

E1 gives j0 and E6 gives j2. Here juxtaposition of starred maps means ordinary function composition, rightmost applied first. Lean statements must instead use explicit categorical composition and native `Cor.graphFunctor` and `PresheafWithTransfers.transfer`.

This matrix check is an assembly step, not the missing geometry. A theorem supplied with E1–E6 as input must not be reported as Theorem 21.6.

## 3. Existing source inventory and actual scope

The following declarations were inspected in source. This audit did not run Lean and does not assert that every current file is kernel-validated at the current worktree. Existing build receipts can be reused only after matching source/dependency identities.

### Presentations and frames

- `Scheme.RelativeCurve.OriginalEtalePresentation` in `Motivic/Aglib/AlgebraicGeometry/RelativeCurve/OriginalEtalePresentation.lean`: actual original etale and puncture pullbacks, a whole marked closed Cartesian square, finite projective compactification, smooth retained relative curve, finite boundary and bad-locus control. This is a local presentation object, not a definition or proof of all arbitrary standard triples.
- `ProjectiveSpace/QuadraticOriginalEtalePresentation.lean`, `nonempty_originalEtalePresentation`: geometric local producer over infinite fields. `PolynomialZeroOriginalEtalePresentation.lean`, `nonempty_polynomialZero_originalEtalePresentation`: whole polynomial-zero specialization. These field/presentation hypotheses must not leak unnoticed into the general 21.6 claim.
- `Scheme.Hom.exists_simultaneous_native_boundary_frames` in `RelativeCurve/SimultaneousNativeFrames.lean`: constructs diagonal and positive-twist frames on one smaller affine source/base, retaining the whole finite boundary.
- `Scheme.Hom.relativeCompactificationGraphLine` in `RelativeCurve/RetainedGraph.lean`: actual graph ideal line on the original compactified relative product; smoothness is needed only on the retained open.
- `Scheme.Hom.relativeFullBoundaryCoordinate_inl` and `_inr` in `RelativeCurve/FullBoundaryCoordinate.lean`: literal coordinate one at infinity and original specified coordinate on the whole marked fiber. These are useful native versions of the compatible boundary scalar data, stronger than a mere abstract Picard-class equality.

### Sections and concrete correspondences

- `Scheme.RelativeCurvePencil.exists_dataOfBoundaryFrames` in `RelativeCurve/SerrePencilData.lean`: chooses actual pairs using Serre; accepts finite projective presentation and boundary twist frames. Its output is `DiagonalSignedPencilProducer.Data`.
- `Scheme.RelativeCurvePencil.dataOfBoundarySections` in `RelativeCurve/SectionPencilData.lean`: proves regularity and finite flatness from genuine section and boundary data; they are not assumed as correspondence-level axioms.
- `relativeCommonPencil_boundary`, `relativePencil_finite_flat`, and `commonPencilStart`/`commonPencilEnd` in the corresponding `RelativeCurve` leaves: actual common product boundary identities and family maps.
- `Motivic.DiagonalSignedPencilProducer.Data`: two section diagrams and actual geometry; `lam`, `psi`, `correspondence`, `endpoints` are the concrete output maps.
- `Motivic.hasCorrectingEndpoints_of_data` in `Normalization/ActualCorrectingEndpoints.lean`: the literal endpoint statement. The one endpoint has sign Γ(α)≫lam − Γ(β)≫psi.
- `Motivic.GlobalBoundaryPencil.correspondence`, `graph_endpoint_correspondence`, `signedCorrespondence_zero`, `signedCorrespondence_one`: finite-flat family and actual full endpoint fibers from equal unit boundary restrictions. This is the promising direct proof mechanism for E4.
- `Motivic.SignedPencilSourceEndpoints.signed_one_source_graphs`: literal endpoint sign λ−ψ, with ψ=Z(d)−Z(n), preserving nilpotent endpoint multiplicities.

### Actions, scope separation, and norms

- `PresheafWithTransfers.transfer_homotopy_endpoints` in `Cohomology/A1/Basic.lean`: HI alone identifies original cylinder endpoint actions; no strict invariance is used.
- `restriction_difference_eq_restriction_of_homotopy` in `Cohomology/A1/SquareDifferenceActions.lean` and `hasRestrictionDifferenceLifting_of_data` in `RelativeCurveLocalLifting.lean`: original-section restriction-difference lifting. This supplies an E6-shaped equation but not E1–E5 for the same maps.
- `SmoothSiteBoundaryOneDivisorNorm.affinePowerOneNorm_affinePowerOneDivisor`, `largeAffineReducedDivisor_norm`, `sheafDivisorChainMap_norm`: actual boundary-one/reduced-torus norm identities. Their target is not the arbitrary relative curve covering of 21.6; do not cite them as that comparison without a proved adapter.
- `FiniteSchemeNormBaseChange.norm_fst` and `normUnits_fst`: actual finite scheme scalar-extension norms, over fields, without reducedness of the finite scheme. This gives a trustworthy lower determinant-norm component, but not yet descent for a general finite non-flat map between normal relative schemes.
- Native Aglib provides actual line bundles, duals, tensor/pullback coherence and ordinary Picard classes. No full relative-Picard/Suslin-H0 comparison was located by this bounded audit. That is a search result, not proof that the needed geometry cannot be obtained by direct pencils.

## 4. Producer-by-producer proof obligations

### G0: faithful geometry input and fixed-parameter section existence

Prefer adapters on the existing actual schemes, graph ideals, compactification maps, and boundary inclusions. Introduce only a small standard-triple predicate/package if no current object expresses the literal input; do not make a second relative-curve hierarchy.

First resolve two genuine scope gaps:

1. A standard triple supplies a proper relative curve with affine boundary neighborhood, not the finite projective presentation required by the current Serre leaf. Either derive the needed projective presentation/ample divisor and boundary-adapted twist, or generalize the section producer using exactly these standard-triple hypotheses.
2. Theorem 21.6 concerns the GIVEN affine X' and Y'. `exists_simultaneous_native_boundary_frames` shrinks parameters, so using it directly proves a further-refinement result, not 21.6. Need section existence on unchanged affine parameters from the specified splitting and affine boundary neighborhood. In particular a line bundle on an affine finite boundary need not be globally trivial just because that boundary is affine. Prove the boundary-adapted ample twist construction, rather than assuming all twists have frames.

This is the first go/no-go checkpoint for the general direct-pencils route. The narrower local-refinement construction may remain useful but must be named and stated accordingly.

### G1: one compatible diagonal lifting pair (E1, E2, E3)

Use the prescribed target diagonal frame. Pull it through the covering's actual marked-fiber isomorphism, and use the etale diagonal decomposition to construct the source diagonal frame (the geometric content of 21.3). Preserve the chosen frame and its canonical scalar in subsequent construction.

Produce λA and λB as actual signed finite-flat divisors with these synchronized boundary values. Construct E1 and E2 by comparing each lifted diagonal divisor with its original graph using the boundary-normalized pencil. For E3 compare the pushforward of the source construction with pullback of the target construction. The correspondence equality must use actual graph composition, finite pushforward and base-change maps, not an unspecified replacement norm.

Deliverable: one simultaneous pair with three explicit homotopies, with no supplied homotopy-equation fields. A pair of independent applications of existing local lifting is not this checkpoint.

### G2: the same correction and E4, E6

On A' times the source compactification, use the same boundary scalar as G1, prescribing one at infinity. Construct numerator/denominator sections and ψ with the sign Z(denominator)−Z(numerator), matching the existing source-endpoint convention.

After forgetting the marked boundary but retaining infinity, the restrictions of those sections agree. `GlobalBoundaryPencil` should then construct the nullhomotopy of ψ≫Γ(u), proving E4. The missing adapter identifies its actual whole zero endpoints with those of this chosen ψ, after postcomposition by the original open inclusion. No abstract equality assumption replaces that identification.

The existing common mixed-product family is the candidate for E6. Instantiate it with the exact G1/G2 choices, preserving the source inclusion rB and square commutativity. The existing endpoint producer is strong evidence for this path, but it must not be re-run with fresh unrelated choices.

### G3: pushforward correction and E5

Prove that the original finite pushforward of this ψ has the target boundary normalization used by λA, then build the target comparison pencil. This requires the marked-boundary norm identity and the precise divisor/pushforward compatibility. E3 may share the same lower norm theorem, so this is a reusable geometric lower layer, not a last-minute algebraic simplification.

Keep the following scope distinctions explicit:

- Published 21.10 assumes normal U,V, finite f, reduced Z,Z', an isomorphism Z'→Z, and etaleness near Z'. The equality of units is on these reduced marked subschemes.
- Finite-flat endpoint schemes may remain nonreduced. Their full local lengths are already supported; reducing endpoint schemes is invalid.
- Reduced marked boundary and nonreduced zero divisors are different roles. The robustness of endpoint cycles does NOT remove the reducedness hypothesis in 21.10.
- If a chosen standard-triple formulation allows nonreduced marked schemes, explicitly pass to reduced marked support with unchanged open square and prove that the given splitting restricts; or prove a stronger scheme-theoretic norm lemma under suitable hypotheses. Do not silently assert that pointwise boundary equality implies equality on a thickening.
- Finite maps between normal schemes need not be flat. The proof must use the appropriate function-field norm and normal extension/descent, or prove the required flatness on the exact neighborhood before invoking determinant norms. Field-base-change norm lemmas alone do not justify arbitrary relative-base norm compatibility.

### Recommended reduced-boundary preprocessing

Reduce the auxiliary marked boundary before selecting any of the three correspondences. This avoids demanding a stronger nonreduced version of 21.10 and appears compatible with the actual native producers:

1. Construct ZX_red with its closed map to ZX and unchanged underlying support. Native `Scheme.IdealSheafData.vanishingIdeal` provides the reduced-induced-closed-subscheme starting point; the exact quotient and reducedness adapters still need implementation/audit.
2. Base-change the ORIGINAL marked Cartesian square along ZX_red → ZX. Because the original marked-fiber map is an isomorphism, its pullback is an isomorphism and gives the new source marked scheme canonically. This retains the full reduced closed scheme, not just residue points.
3. Restrict the specified splitting through the actual module pullback and graph-ideal comparison. Preserve its canonical section coordinate, not just an abstract line-bundle class.
4. The complements A and B, hence Q and Q', do not change. Properness, normal compactifications and etale retained maps are untouched. Finiteness, disjointness and the affine boundary neighborhood persist.
5. Rebuild ALL synchronized frames and section pairs using this reduced auxiliary boundary. Existing `relativeFullBoundaryCoordinate_inl`/`_inr` and common-boundary lemmas accept arbitrary actual closed Cartesian data; the finite-flat construction uses geometric range coverage plus exact unit boundary values. None of the inspected statements requires a thickened auxiliary marked locus.

This is a recommended proof reduction, not yet a Lean theorem. Do not mix a newly reduced norm argument with independently chosen old thickened-boundary sections. Zero-divisor endpoint schemes are never reduced: their nilpotents and cycle lengths remain exactly as constructed.

### G4: assembly and actual corollaries

After G1–G3, use HI endpoint actions to assemble a genuine homotopy in the native complex category, with the original square-induced map. A lower matrix helper is reasonable but its terminal consumer must instantiate the proved simultaneous producer.

Then obtain identity-specialization contractibility and split exactness under the full hypotheses. Only after that implement 21.11: finite-set affine neighborhoods, inherited splitting, retention of the complete marked fiber, and the actual induced upper distinguished square. Current point-indexed frame neighborhoods do not by themselves prove a simultaneous finite-set neighborhood theorem; audit semilocal line-bundle triviality and its finite-set API separately.

## 5. Route decision and parallelism

Prefer direct actual section/pencil constructions: the repository already represents their maps, full finite-flat supports, diagonal ideals, boundary scalar coherence and graph endpoints. A new full relative-Picard/H0 comparison would require relative classes, divisors, surjectivity, homotopy-kernel identification, pullback and norm functoriality; that is materially larger than a wrapper around the ordinary Picard group.

This preference is conditional on resolving G0 without weakening the theorem. If boundary-adapted section existence or norm compatibility cannot be supplied with available geometry, stop and reassess that exact point. Do not claim general 21.6 from a theorem that further shrinks X' or adds a projective/frame premise.

After review, independent work can be split into:

- Geometry/section lane: G0 and compatible splitting/diagonal frames.
- Boundary correction lane: G2 and the concrete E4 endpoint adapter.
- Norm/comparison lane: G3 and shared E3 lower comparison.
- Assembly lane: exact square complex and signs, but final theorem waits for G1–G3.

Existing original-presheaf Epi work continues unchanged in parallel. It consumes a weaker restriction-lifting theorem and need not wait for the full simultaneous nullhomotopy. Conversely its completion does not certify 21.6.

All compiler/build outputs remain serialized to protect shared outputs. No pin, cap, heartbeat, linter changes or broad rebuilds.

## 6. Proposed ownership and acceptance

No existing Epi correction, normalization or coordinate leaf is to be modified by this lane without agreement with its owner. New lower generic geometry belongs under the existing native `AlgebraicGeometry.Scheme` owners; actual correspondences and HI actions under their existing Motivic namespaces. Proposed leaf names are provisional until G0 fixes their exact content:

- `RelativeCurve/CoveringBoundaryFrames.lean`
- `RelativeCurve/BoundaryAdaptedSections.lean`
- `Correspondences/CoveringDiagonalHomotopies.lean`
- `Correspondences/CoveringCorrectionHomotopies.lean`
- `PresheavesWithTransfers/DistinguishedSquareHomotopy.lean`
- a meaningful `MotivicTest/StandardTripleSplitting.lean` terminal consumer.

Do not create speculative empty source directories. Maintained prose is English; authored headers use `Authors: kangxyz`. Lower geometry must not import strict-A1 or downstream consequences.

Acceptance milestones:

1. Exact standard-triple/covering input bridge and fixed-parameter section theorem, with no hidden shrinking.
2. One compatible λA,λB pair satisfying E1–E3 geometrically.
3. One ψ compatible with those maps, with E4–E6 geometrically constructed.
4. Actual complex-map nullhomotopy for arbitrary HI presheaves in unchanged coefficient universes.
5. Identity corollary and, separately, finite-set local refinement.

Each accepted terminal result needs selective compilation, a meaningful actual consumer, and final declaration/text/source checks plus mechanical transitive axiom rejection (standard axioms only). Use compatible existing evidence and test only affected closures; helper progress does not trigger separate full audits. No push is authorized.

## 7. Current edit and validation status

Before the instruction to pause implementation arrived, one new uncompiled draft was written:
`Motivic/AlgebraicGeometry/PresheavesWithTransfers/BoundaryPencilHomotopy.lean`.
It connects `GlobalBoundaryPencil`'s original endpoint correspondences to equality/zero difference of HI transfer actions. It explicitly does not claim identification with the chosen ψ or any full 21.6 nullhomotopy. It is not an accepted milestone and remains untouched while this plan is reviewed.

No StandardTriple replacement structure, six-equation input theorem, source mutation outside that one draft, compiler execution, commit or push was made by this lane. The present plan and local PDF renders are outside the repository.
