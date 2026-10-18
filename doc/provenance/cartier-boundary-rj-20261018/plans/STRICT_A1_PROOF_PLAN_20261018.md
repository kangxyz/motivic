# Strict A1: literature-checked remaining proof plan

Date: 2026-10-18. This is an implementation plan, not a completion certificate.
The unconditional strict A1 theorem is still open. Source candidates, production
compilation and accepted terminal consumers are distinguished below.

## 1. Decision and scope

Keep the existing finite-degree/local-rank strategy. Do not restart with a Gersten,
Rost--Schmid or motivic-category proof: the required independent infrastructure is
not presently available, and several familiar consequences already depend on
strict invariance. Prove the first endpoint for infinite perfect fields, with the
current coefficient universe `u + 1` and ordinary `HasExt` assumptions retained.
A finite-field extension is a later theorem, not an inferred corollary.

The target is bijectivity of the **original projection pullback**
`H^N_Nis(X,F) -> H^N_Nis(X × A1,F)` for every HI Nisnevich sheaf with transfers F.
An abstract group equivalence, or a result with a supplied puncture-Mono family,
is not this target.

Implementation changes were paused during this review. A running bounded
Cartier build was allowed to terminate; its fourteen required native geometric
prerequisites compiled, but the new boundary-zero endpoint did not.

## 2. Primary references and their precise role

Controlling reference: [MVW, published Clay edition](https://www.claymath.org/wp-content/uploads/2022/03/Motivic-Cohomology.pdf).
The bibliographic checkpoints are 21.6/21.11, 22.8, 23.5--23.12 and 24.1--24.4.
Definition 23.6 fixes quotient order; 23.10 concerns the cylinder; 23.11 is excision;
23.12 provides local identifications compatible with products. Proposition 24.3
separates coefficient-change injectivity from the Leray edge, treating degree one
separately. Its published pages are 198--199 (PDF viewer pages 213--214), not the
pagination of the older Rutgers draft. Those diagrams were visually checked.

[Author-maintained errata](https://sites.math.rutgers.edu/~weibel/Books/MVW.errors.pdf)
were checked: the current list has no entry for Lectures 23--24. This is not a
substitute for checking the proof obligations below.

[Stacks 59.46](https://stacks.math.columbia.edu/tag/04E1) gives a small-etale
closed-support model via neighborhoods and stalks. It is not automatically a
Nisnevich theorem: our point comparisons must retain full field-valued marks.
[Stacks 59.79.4](https://stacks.math.columbia.edu/tag/0AEG) explains the derived
support equivalence after exactness; we only need the smaller exact-adjunction
Ext comparison, not a new derived recollement development.

The remaining sections specify our own source-level proof contracts and
acceptance obligations; they are not a transcription of these references.

## 3. Evidence baseline

Accepted endpoints already include:

- Generic-base positive-degree vanishing and transport to the actual whole
  cylinder, then unconditional rank-zero original pointed-colimit vanishing.
- Actual smooth Cartier choice at a positive-local-rank point; finite smooth
  stalk rank; actual open localization and conditional positive-rank reduction.
- Canonical sheaf contraction-to-boundary Mono over arbitrary fields.
- Exact comparison between the original-presheaf boundary and the old sheaf
  boundary, including the canonical-map square.
- BIG transfer and literal SMALL ordinary contraction-sheaf zero for the
  original positive-degree cohomology presheaf, with that degree's HI explicit.
- Original coefficient restriction Mono for a dense Cartier complement over
  infinite fields, and the native density theorem.
- Actual split-Noetherian support unit, exact closed direct image and original
  ordinary-cohomology comparison (accepted 00:55 UTC); full marked inverse-image
  composition and outside-support direct-image zero are in the same audited scope.

Production-only, not yet terminally accepted:

- General-presheaf etale boundary excision/localization.
- Several actual two-correction geometric maps and whole-zero identities.
- The native common etale Cartier chart with both complete closed-fiber squares.

The actual Cartier/Rj join is now accepted with current positive-degree HI
and original EPI-P explicit (01:36 UTC).
Still unaccepted: original-presheaf boundary Epi; chart/product naturality of the accepted support comparison; product-compatible degree-one
lifting; original cohomological puncture Mono; unconditional final induction.
A file containing the intended theorem is not evidence that it compiles.

## 4. Noncircular induction contract

For a fixed N > 0 assume `HI(H^q(-,G))` for every positive q < N
and **every HI Nisnevich transfer sheaf G**, not just the current F.
The contraction is already an HI sheaf by its original t=1 splitting; do not
invoke a later higher-cohomological contraction theorem to establish this. This permits
using the degree N-1 hypothesis for the contraction F_-1 when N > 1.

1. Those hypotheses make the original `P_q = H^q(-,F)` HI for 0 < q < N.
2. Only these lower P_q are used to obtain `R^q j_* = 0` for 0 < q < N.
3. Establish the original degree-N puncture restriction Mono by the two
   separate mechanisms in sections 7 and 8.
4. Induct on the finite local rank of the original marked base. Rank zero is
   accepted. Positive rank uses a chosen smooth Cartier divisor, lower-rank
   punctured vanishing and the newly proved Mono.
5. Detect zero on all marked fibers of all small test objects; deduce the
   actual `R^N pi_* F = 0`.
6. Use the existing finite Leray projection comparison to identify the original
   global degree-N pullback as an isomorphism.

Do not assume HI(P_N) to prove step 3. Do not apply the completed strict theorem
(or Gersten consequences) to F_-1. Degree zero is the original HI assumption.
Perfectness is used for smooth divisor selection, never to assert that an
arbitrary residue or marking field is perfect.

## 5. Package A: original-presheaf canonical boundary Epi

The standard-triple technology is a genuine dependency, not an optional
shortcut being avoided. The implementation chain is actual curve presentation
and boundary frames -> signed finite-flat pencil endpoints -> original-section
restriction-difference lifting -> canonical boundary Epi -> strict A1 assembly.
Reusing concrete producers instead of packaging the full general standard-triple
theorem does not remove any required lifting obligation. The terminal Epi test
must instantiate those producers, not accept an abstract lifting family.

Contract: for every original HI presheaf with transfers P and smooth base V,
prove Epi of `OriginalPresheaf.contractionToBoundary V P`. Form the objectwise
original quotient first, then ordinary small-site sheafification, then genuine
closed inverse image. Replacing P by its sheafification earlier is forbidden.

Remaining constructive sequence:

1. Start with an arbitrary original punctured generator and an actual closed
   point of its original zero fiber. Obtain an integral affine whole-zero
   refinement retaining the full closed scheme, not only a point.
2. Construct the polynomial closed-point presentation and both HI restriction
   corrections. Preserve their original pullback maps and additive signs.
3. Identify the actual Laurent puncture, cylinder, corrected ambient source and
   original zero morphism. Use the canonical geometric image-sieve lemma on the
   original section, not a supplied local-lifting family.
4. Prove that the resulting image arrow is exactly the actual composite base
   open into the original zero fiber. It must be an open immersion containing
   the chosen closed point.
5. Apply Jacobson open-cover detection, then the actual generator criterion for
   Epi. Residue-splitting etale arrows over closed points alone are not a cover.
6. Specialize through the accepted source/target comparison square. Combine
   with the accepted sheaf Mono to obtain a genuine canonical sheaf isomorphism.

Main sources: `PresheafContractionBoundaryEpi`,
`OriginalPresentationCombinedCorrection`, `PresheafBoundaryPolynomialImage`,
`PresheafBoundaryGeometricRefinement`, `PuncturedCylinderCoordinates`.
The checked lower chain constructs the weaker original-section restriction
lifting needed here; it is not a blanket theorem that every distinguished-square
Mayer--Vietoris complex is split exact or a full six-equation chain homotopy.
The next compiler frontier is the lambda/cylinder normalization and its actual
consumers. Even if remaining errors look syntactic, completion is not assumed.

Acceptance: unchanged original P, no added lifting/excision/Epi premise, actual
open-image cover, original canonical map; test plus transitive axiom audit.

## 6. Package B: boundary zero to higher-open-image zero

This exact twelve-file bridge passed terminal validation at 01:36 UTC,
including all 103 selected declarations. The EPI-P and current-degree HI
premises below remain explicit; the Epi producer itself is still open.

Contract: for an actual smooth Cartier pair `(Y,Z)` with complement j and each
0 < q < N, prove zero of the genuine `R^q j_* (F|U)`.

1. Apply accepted literal SMALL contraction zero to P_q under lower-degree HI.
2. Apply Package A on the literal cylinder. Transport boundary zero through the
   two actual etale comparisons of a local Cartier chart.
3. Use the actual graph natural isomorphism between transfer cohomology and the
   ordinary cohomology presheaf. Identity groups do not make graph maps defeq.
4. At a closed marked point compare the original punctured colimit with the
   boundary fiber: ambient positive cohomology germs vanish; the literal
   quotient projection becomes invertible after taking the point fiber.
5. Identify that punctured colimit with the genuine derived direct-image fiber,
   pinning the isomorphism by its value on the original quotient projection.
6. At an open marked point use the actual open pullback/effacement. Detect zero
   using all marked test-object fibers, not only the base's residue points.

Sources: `PresheafBoundaryPointComparison`, `PresheafBoundaryOpenSupport`,
`SheafCohomologyCartierBoundaryZero` and the two general-P excision leaves.

Acceptance: one meaningful consumer from actual lower-degree HI plus proved A
through the actual Cartier chart to the genuine higher image. While A is open,
its Epi hypothesis must remain visibly explicit. This package closes only the
Leray side of the puncture argument.

## 7. Package C: actual ambient-cokernel support bridge

Core steps 1--5 below are now accepted on the stated split-Noetherian scope.
The naturality/application joins in the following subsection remain open.

Let `C = coker(F -> j_* j^* F)` on the ambient scheme. The LES contains C,
not merely `i^-1 C`. The actual unit `C -> i_* i^-1 C` must be proved invertible.

Use the smallest available geometric setting: a split closed immersion i into
a Noetherian ambient E, with a specified retraction p and `i ≫ p = id`, and the
actual quasi-compact open complement. Do not first build arbitrary global
closed-support recollement.

1. Finish the actual closed marked-neighborhood comparison. Extend etale
   neighborhoods by p-pullback; equalize closed-fiber arrows after a genuine
   ambient refinement. Preserve all marking fields and structural maps.
2. Prove direct-image zero on the complement from the literal empty pullback.
3. Derive exactness of the genuine closed direct image from point fibers, and
   the supported unit isomorphism from its actual unit comparison.
4. Show the original C restricts to zero on the complement, using its actual
   cokernel definition, not an extra support hypothesis at the application.
5. Use the exact image adjunction to identify ordinary Ext cohomology. Pin the
   comparison as coefficient change by the actual unit followed by the original
   ordinary edge map. No replacement cohomology theory is permitted.

Sources: `FiniteEtaleSplitClosedComap`, `...SupportUnit`, `...ImageExact`,
`...Cohomology`, with `FiniteEtaleDirectImageOpenSupport`.

### Required naturality, not optional cleanup

Objectwise bijections are insufficient. The proposed equation
`ordinarySupportComparison_eq_inverseImage` anchors the map, but a remaining
source-coherence square for `inverseImageSourceIso` must be proved under
composition/base change. It must commute with the actual free-source objects,
canonical inverse-image composition iso and actual base-change iso. Then derive
coefficient and test-object naturality using native Ext composition identities.
The chart/product map must be the actual boundary coefficient morphism.

## 8. Package D: separate degree-one and higher-degree LES arguments

Always distinguish the **normal Cartier coordinate t** from the **homotopy
parameter h**. Choose/refine the Cartier chart on the base first, then take
its product with the whole A1_h. Arbitrarily shrinking inside E × A1_h is not
an admissible substitute for preserving the whole cylinder in the induction.

Choose a common etale chart E mapping both to the original base and to Z × A1_t,
with the complete zero fiber identified with Z. The map to Z × A1_t supplies
the retraction needed in C. After product with A1_h it remains split.
A further marked etale O-prime -> O killing a base class lifts by the literal
pullback E-prime = E ×_O O-prime; its closed section retains the full field mark.
All changes must induce actual allowed refinements of the original pointed
base index. This chart-to-original-colimit interface needs its own consumer.

### N > 1

Use canonical boundary identification, C and naturality to identify the LES
left term on E × A1_h with degree N-1 cohomology of F_-1 on Z × A1_h.
Use lower-degree strict invariance for F_-1, then ordinary pointed-base
acyclicity and split-closed initiality, to kill the original representative
after an allowed base refinement. This is a germ argument, not a claim that
every finite-stage cohomology group is zero.

### N = 1

Preferred smaller implementation: use the actual support units on the two
literal normal-cylinder models only. The original closed-unit/projection square
and invertible boundary projection make the actual ambient cokernel projection
map invertible. Transport it through true etale ambient-cokernel excision and
the actual product Beck--Chevalley map, then identify it with the literal chart
product pullback. This avoids a fresh closed-unit/excision coherence theorem on
the chart for degree one. The model cokernel's open restriction must still be
proved zero, not supplied as an extra final hypothesis.

Positive-degree vanishing is unavailable. First use A plus Mono to obtain an
actual boundary sheaf isomorphism. A boundary section on the whole Z × A1_h
then has a contraction antecedent; HI(F_-1) makes it a pullback of a base
section. Apply the inverse ACTUAL base support unit/H0 comparison to turn that
boundary section into a section of the ambient cokernel. Only then use the
ambient cokernel projection Epi to lift it Nisnevich-locally on E. Pull the lift over the whole A1_h.

Two different epis are involved: the canonical boundary comparison and the
ambient cokernel projection. Neither permits silently taking globally
surjective sections on an arbitrary finite-stage test object.

Prove the literal product/excision square for q and q × id_A1_h, retaining
original cokernel projections and closed units. The cylinder kappa projection
square alone does not supply that square on an arbitrary etale Cartier chart.
Establish c1 = actual product pullback(c0) on the ORIGINAL split chart first.
After the local quotient lift on E-prime, restrict that established equality and
the original SES to E-prime × A1_h. This avoids applying the split support theorem
again: the new neighborhood need not retain a retraction. A new split chart is
only a fallback if an implementation insists on recomputing support there.
Use it to identify the lifted section with the exact LES map. For N=1 the
canonical H0 support comparison suffices; higher Ext naturality is for N>1.

Acceptance: surjectivity on the original marked colimit of the LES preceding
map, hence injectivity of coefficient change. No global untwisted Cartier
purity or unproved finite-stage section surjectivity is assumed.

## 9. Package E: puncture Mono and final assembly

Factor the original restriction into coefficient change followed by the actual
open-image edge map. D proves the first factor monic. B and the existing finite
Leray edge theorem prove the second monic using exactly 0 < q < N. No vanishing
of R^N j_* is needed for this injection.

Identify the composite with the unchanged original pointed-cylinder restriction.
Discharge `SmoothCartierPunctureRestrictionMono`; do not merely pass it as an
argument. Then compile and validate `StrictA1DegreeInduction` against the
unconditional producer, using the contract in section 4.

Final acceptance requires the original projection pullback, all N and all
smooth X in the stated field/universe scope, no theorem-family inputs standing
for A--D, no new axioms or `sorry`, and an affected actual terminal consumer.

## 10. Parallel work after plan delivery

- A: original-P Epi and exact sheaf specialization.
- B: actual Cartier boundary-zero and point/Rj join, conditional on A until A
  is accepted. Keep source repairs separate from mathematical acceptance.
- C: split support unit/exactness/original cohomology.
- D1: cylinder projection and product-etale excision compatibility; N=1 lift.
- D2/E: exact chart-to-original-index transport and higher-degree LES assembly;
  final rank/degree source can be checked conditionally but not called complete.
- Integration: free-source inverse-image coherence, actual map identities,
  terminal consumer and truthful status documentation.

Parallelism concerns independent proof design/source ownership. Compiler and
mutable build outputs stay serialized. Each lane reports a useful result or
mathematical blocker, not a stream of individual normalization edits.

## 11. Milestones and stopping checks

M1: canonical original-P Epi plus exact sheaf isomorphism.
M2: actual lower Rj window on smooth Cartier complements.
M3: actual supported-cokernel cohomology bridge with required naturality.
M4a: unconditional degree-one original puncture Mono from A, the H0 part of C,
and product/chart lifting. Its positive Rj window is empty: do not wait for B.
M4b: N>1 left-term zero and puncture Mono on unchanged marked colimits, using B.
M5: unconditional puncture Mono, then infinite-perfect strict A1.

M2 and M3 may complete independently. M4a/M4b are the principal integration risks;
source presence in A--C does not make it automatic. Revisit the plan if a chart
refinement loses product shape, original-map naturality cannot be supplied, or
a proof invokes current-degree HI. Do not hide such a failure behind a new
hypothesis or a broader replacement abstraction.

At each accepted milestone deliver full source with exact scoped validation.
Keep the existing hourly source checkpoint obligation, labeling drafts honestly.
Do not update dependency pins or push without the applicable user authorization.

## Subsequent parallel scope authorization

The user separately requested the complete standard-triple technology, then
requested its own literature review and proof plan before implementation. That
plan was delivered at 00:58 UTC and is maintained in
`STANDARD_TRIPLE_PROOF_PLAN_20261018.md`. At 01:00 UTC the user also authorized
necessary partial relative Picard interfaces in parallel. These upstream lanes
do not block the already constructed narrower original-P lifting route.
