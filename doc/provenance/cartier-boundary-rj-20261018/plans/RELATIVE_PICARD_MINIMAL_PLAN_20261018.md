# Minimal relative Picard interface plan

Date: 2026-10-18. Minimal source/consumer plan reviewed; scoped implementation authorized at 01:05 UTC.

## Decision and exact consumer

Implement actual boundary-framed line bundles and their isomorphism classes, with the tensor and restriction operations needed to express the existing normalized Serre divisor-pair construction. Do not implement a Picard scheme, cohomological comparison, full Suslin-H0 comparison, or general representability theorem in this tranche. An initial class type need not carry an AddCommGroup until a real consumer needs subtraction.

The first terminal consumer is `Scheme.CoherentGraph.exists_normalized_boundary_divisor_pair` in `RelativeCurve/NormalizedDivisorPairs.lean`. Under its UNCHANGED finite-projective-presentation and all-twist-boundary-frame hypotheses, it produces actual sections s of T tensor M and t of T, with boundary-invertible restrictions and exact equation

    pullbackSectionMap z s ; pullbackTensorMap z T M
      = tensorUnitSection (pullbackSectionMap z t) E.inv.

Associate to each section s the original line bundle equipped with frame `(asIso (pullbackSectionMap z s)).symm`. The equation above proves that its framed class is the tensor of the framed class of t and the original pair (M,E). Thus the native signed divisor representative retains the intended relative class, without merely postulating a class-comparison field. Return the SAME s,t, SectionDivisorFiniteFlat witnesses, and exact normalization equation. The theorem is a compatibility adapter to the actual producer, not arbitrary divisor surjectivity.

Second useful consumer, after the first works: changing two frames on the same line bundle is controlled by the literal boundary automorphism E.inv ; F.hom; forgetting part of the boundary can make this automorphism the identity. This is the class-level bookkeeping in MVW 11.10/11.16 and 21.9, and must retain actual boundary units, not merely existence of an isomorphism. It should not duplicate already proved CommonBoundaryCoordinate scalar identities.

## Source inventory and existing canonical objects

- Aglib `Modules/Invertible/Basic`: actual LineBundle as locally rank-one module sheaf, ordinary lineBundleSetoid and LineBundleClass.
- Aglib `Modules/Invertible/Tensor`, `TensorAssociator`, `Dual`: native tensorLineBundle, actual tensor maps/unit/associator/evaluation, ordinary PicardGroup.
- Aglib `Modules/Invertible/Pullback`, `PullbackTensor/Local`: pullbackLineBundle, actual invertible pullbackTensorMap, pullbackLineBundleTensorIso, additive ordinary pullbackHom.
- Aglib `Modules/Pullback` and local `TensorSectionPullback`: actual pullbackComp/pullbackUnitIso coherence, pullbackSectionMap_comp and pullbackSectionMap_tensorUnitSection.
- Local `BoundaryTensorSections` and `SectionPairNormalization`: literal tensor section operations and exact prescribedPair_normalized equation.
- Local `OpenBoundaryFrame`, `OpenBoundaryCoordinate`, `OpenBoundaryCoordinatePullback`: native open-restriction frame and canonical coordinate preservation, including original unitEndomorphismPullback.
- Local `RelativeCurve/BoundaryFramePullback`, `FullBoundaryCoordinate`, `CommonBoundaryCoordinate`: actual graph ideal frame and whole boundary scalar identities, including infinity=1; no replacement line classes.
- Local `RelativeCurve/SerreDivisorPairs` and `NormalizedDivisorPairs`: actual whole-zero finite-flat properties and normalized section pair producer.
- Local `Modules/Invertible/DualTwistedIdeal*` and `MixedPrescribedPencilBoundary`: exact global line isomorphisms and mixed-product boundary equality for the existing E6 path.
- Local `Correspondences/RelativeCartierDivisor`, `GlobalBoundaryPencil`: actual signed correspondences, original endpoints, full finite-flat local lengths.

Bounded searches for relative/framed class objects in Motivic and the Aglib algebraic-geometry subtree, combined with inspection of these owners, found no competing relative framed-line quotient. This is a bounded inventory, not a global nonexistence claim.

## Minimal proof DAG and provisional files

1. `Modules/Invertible/BoundaryFramed.lean`:
   - `BoundaryFramedLineBundle (i : D -> C)`: native LineBundle C plus iso i*L -> O_D.
   - Frame-preserving iso: native e : L.val ≅ M.val with `(pullback i).map e.hom ; M.frame.hom = L.frame.hom`.
   - reflexive/symmetric/transitive relation, class quotient, exact class equality iff a frame-preserving iso, forgetful map to the EXISTING PicardGroup.
   - transport along actual line isomorphism; section-induced frame when the actual pullbackSectionMap is an isomorphism.
   No second line-bundle implementation; no closed immersion hypothesis is needed for these elementary constructions.

2. `Modules/Invertible/BoundaryFramedTensor.lean`:
   - tensor pair built from native pullbackLineBundleTensorIso, tensorSheafIso of the two given frames, and native tensorSheafLeftUnit on O_D.
   - tensor descends to classes by the native tensorSheafIso and pullbackTensorMap_naturality.
   - forgetful map sends this operation to ordinary Picard addition.
   - MAIN algebraic lemma: the literal normalized s,t,E equation implies the framed section object for s is frame-preservingly isomorphic to tensor(section-framed t,(M,E)); underlying module iso is the actual identity on tensorLineBundle T M, not an unspecified witness.
   Proof uses tensorUnitSection definition, invertibility of boundary section maps, native tensor comparison and cancellation. It neither needs nor claims the full relative group laws.

3. `RelativeCurve/BoundaryFramedDivisorPairs.lean`:
   - instantiate step 2 with the EXISTING `exists_normalized_boundary_divisor_pair` output and return exact sections, finite-flat zeros, and framed-class equality together.
   - concrete terminal test invokes this producer with its genuine geometric hypotheses, not an extra supplied framed-class equation.
   This is the required acceptance point before further interface expansion.

4. Only after that acceptance, `Modules/Invertible/BoundaryFramedPullback.lean`:
   - first forget part of boundary by actual composable maps D' -> D -> C, using pullbackComp and pullbackUnitIso;
   - actual commutative-square pair pullback (not necessarily Cartesian), with canonical comparison through pullbackComp and the supplied square equality;
   - preserve frame-preserving isos and forgetful ordinary Picard pullback; identity/composition laws if required by a concrete chosen consumer.
   - recover the original transported boundary coordinate in a section-induced frame using pullbackSectionMap_comp. Cross-check openRestriction against the existing openBoundaryFrame rather than defining a parallel model.

5. Optional subsequent tranche only if requested by the standard-triple consumer: dual frame via native dual pullback/evaluation, additive group laws, same-underlying-line frame-difference formula. Proving all monoidal coherence before step 3 would delay the actual consumer without solving geometry.

Precise provisional namespace: `AlgebraicGeometry.Scheme.Modules.Invertible`, with a nested `BoundaryFramedLineBundle` namespace for operations. Class name should explicitly say class, not claim a cohomological Picard comparison. The three native interface files and their concrete consumer form one bounded implementation scope.

## Literature check

Controlling primary source: MVW published Clay edition, https://www.claymath.org/wp-content/uploads/2022/03/Motivic-Cohomology.pdf. Read local published PDF text at the following numbered results:

- 7.10 identifies relative Picard elements with actual (L,t) up to frame-preserving isomorphism; operation is tensor. This supports the chosen representation, not a Lean theorem comparing it with sheaf H1.
- 7.11 gives the boundary-units / relative-Picard / ordinary-Picard exact sequence. We do not claim this full sequence in this tranche.
- 7.12 A1 invariance requires normal ambient and REDUCED boundary.
- 7.15 uses extension of the boundary trivialization to a neighborhood and the associated rational Cartier/Weil divisor to obtain relative divisor representatives. Implementing only framed classes does not prove that extension/geometric representation theorem.
- 7.16 identifies H0sing with relative Picard for smooth quasi-affine relative curves with good compactification; kernel uses an explicit boundary-one rational pencil. No assertion of this comparison is authorized by the partial interface.
- 7.22--7.24 give boundary norm and divisor pushforward compatibility for finite maps of normal compactifications; finite does not imply flat.
- 11.8--11.10, 11.15--11.16 use boundary forgetting and differences of trivializations.
- 21.7--21.9 require compatible choices of lambda_A, lambda_B and psi; class arithmetic alone does not identify actual homotopy endpoints.
- 21.10 has finite normal maps, reduced auxiliary marked schemes, marked-locus isomorphism and etaleness near that locus. Nonreduced zero endpoints and their lengths are NOT reduced in this proof.

## G0 and norm boundaries

The standard-triple lane confirmed the general G0 gap: published 21.6 keeps given affine X',Y' and permits arbitrary proper standard triples. Existing all-twist frames / finite-projective presentation have not been derived from those hypotheses. Neither quotient classes nor the restricted adapter above removes that gap. A relative-Picard route instead requires the actual neighborhood trivialization plus Cartier/Weil divisor representative and the H0 kernel theorem; these are substantive additional geometry, not a wrapper.

The separate `Motivic/Aglib/RingTheory/FiniteAlgebraMarkedNorm.lean` candidate concerns the residual finite-algebra marked-branch determinant calculation. Nonflat normal-scheme norm base change and actual divisor pushforward remain open. This lane will not implement any norm independently; later framed-norm adapter must consume the exact proved geometric theorem and preserve original units/maps.

## Acceptance and execution constraints

The first three production leaves and their actual consumer passed terminal validation at 01:22 UTC, including all 69 declarations, standard-axiom checks, and exact-file text/source checks. Pullback, group laws, norm and Suslin-H0 remain outside this accepted scope. Use fixed pins/caps, incremental selected leaf builds, and meaningful terminal consumer plus standard-axiom audit. Do not edit frozen leaves or change existing producers to weaken their geometric hypotheses. Compiler-integrated lint stays enabled; independent lint/test/trust checks belong to final owned-scope validation, not each helper.
