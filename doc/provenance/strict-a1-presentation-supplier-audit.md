# Strict A¹ presentation supplier: checked boundary and remaining route

Status: frozen after the checks completed on 2026-10-17. This is a proof audit, not a claim that general presentation or purity is finished.

## 1. Exact consumer obligation

The existing `ContractionBoundarySheaf.contractionToBoundary hF` targets the genuine small-Nisnevich inverse-image boundary sheaf. To prove local surjectivity, a section on the puncture of an arbitrary étale neighborhood of the zero section must, after allowed refinement, become a section from a Zariski zero-neighborhood modulo a section extending across zero.

An adequate weakest geometric/action output is this. Start with an actual distinguished square `(X,Y,A,B)`, a selected point of `Z=X\A`, and the original étale map `p:Y→X`. Produce smaller affine neighborhoods `X'` and `Y'`, still a distinguished square with the whole closed restriction `Z∩X'`, such that every original section on `B` restricts to a difference of a section on `A'` and one on `Y'`. Original restrictions and their signs must be retained. This is local Mayer–Vietoris surjectivity, not global quotient excision.

`ZeroNeighborhoodLocalLifting.exists_zeroNeighborhood_local_lifting` already covers **every affine Zariski open** in `A¹_R` containing the entire zero section. It is not restricted to monic or principal opens. It supplies the subsequent cylinder-to-Zariski-neighborhood lift after one original-base principal shrink. The missing step is the arbitrary étale representative above.

`SectionQuotientNisnevichExcision` proves relation reflection and the actual quotient restriction is monic for a distinguished square. It does not prove surjectivity. `BoundaryEtaleExcision` is actual sheaf excision; this also does not assert global section-cokernel surjectivity.

## 2. Checked actual finite-coordinate supplier

Let k be infinite, R a smooth affine domain over k, I a nonzero ideal, and p_i a finite family of actual primes. Suppose each actual residue cotangent space has rank d+1.

The checked construction, before the final rank-bound integration, takes the honest bound `trdeg k R ≤ d+1` and produces one

`ψ : MvPolynomial (Fin (d+1)) k →ₐ[k] R`

with all of the following:

1. ψ is finite on the original R.
2. `quotient(I) ∘ ψ ∘ rename(Fin.succ)` is finite on the original, possibly nonreduced R/I.
3. Near every p_i, the same full ψ is actually étale.
4. On the same principal neighborhood, its literal last d coordinates are standard smooth of relative dimension one.

No coordinates, initial determinant, quotient presentation, elimination relation, or good compactification is input. Main directly checked endpoint:
`Algebra.exists_finite_bad_locus_curve_projection`, in `RingTheory/Etale/FiniteBadLocusProjection.lean`.
Its direct test includes the standard-foundation axiom audit.

The proof uses the SAME maps throughout: constructed simultaneous differential coordinates, an actual polynomial presentation with these tail coordinates, induction on excess generators, a relation derived from native transcendence degree, parameterized finite elimination preserving actual residue minors, and a final elimination on R/I whose deleted coordinate is retained in the finite ambient map. The actual initial full-chart/polynomial-automorphism factorization proves the final étaleness.

Two checked auxiliary facts now remove the explicit dimension estimates mathematically:

- `Ideal.trdeg_quotient_le_of_ne_bot`: nonzero ideal in a domain decreases a finite native trdeg bound by one. The quotient need not be reduced or a domain.
- `Algebra.trdeg_le_of_residue_cotangent_finrank`: smooth domain R and one actual prime with cotangent rank n give `trdeg k R ≤ n`. No infinite-field or chosen-coordinate assumption.

The last combination into the finite-family endpoint is deliberately not implemented after the freeze. It must require `[Nonempty ι]`, or a separate witness prime: a merely finite family may be empty, making rank hypotheses vacuous. All constituent statements and direct audits are checked.

## 3. Checked normalization ingredients, and what they do NOT give

`NormalFunctionFieldExtension` constructs the actual extension from the original function field of a normal integral source to an integral target over the base, with its literal base square and uniqueness. The finite ambient map is not falsely required to be smooth or étale everywhere.

`GenericallyEtaleCompactification` constructs the finite normalization and open inclusion of the original source from normal integral source and target, locally Noetherian normal target, dominant separated quasi-finite finite-type source map, and the **actual function-field map** finite étale. These last generic finite/étale facts are explicit hypotheses of this ingredient. They have not yet been derived and joined for the constructed coordinate map. This ingredient is not a finished compactification producer.

`FiniteChartBoundary` proves that relative normalization adds no boundary over a chart where the original map is integral. If the source lies entirely over that chart, its image is exactly the inverse image of the chart. This is an actual normalization/base-change proof and is the correct way to exclude vertical boundary over the finite affine chart; dimension heuristics are unnecessary there.

Still required for the actual proper-cover supplier:

1. Derive dominance and the finite étale function-field map from the actual finite coordinate map and its nonempty étale principal chart.
2. Specialize the normalization to the new `P¹_T`, retaining the literal affine map and original étale neighborhood. Derive, rather than assume, the finite compactified comparison map.
3. Use the finite-chart equality and the original missing-neighborhood image to prove the **entire** boundary finite over T, not just a finite subset.
4. Produce smooth retained curves over T while keeping the entire retained closed Z disjoint from the boundary.
5. Produce the affine neighborhood containing boundary union Z. The consumer's common-base boundary frames and relative Serre machinery then apply.

Step 4 remains the genuine simultaneous presentation issue: smoothness at the chosen points alone does not control every point in their T-fibers.

## 4. Primary route and precise assumptions

Primary reference: [MVW, Lectures on Motivic Cohomology](https://www.claymath.org/wp-content/uploads/2022/03/Motivic-Cohomology.pdf), printed pp. 86–88, 175–182, 189, 192–194.

MVW 11.17 assumes an infinite field and connected smooth quasi-projective W with a proper closed subset. Its quadratic embedding and general projection control smoothness along the whole selected fibers; graph closure, shrinking, and a very ample section give the triple. Definition 21.1 requires a finite compactified map, étaleness on retained opens, and the closed isomorphism. Corollary 21.11 yields local null-homotopy for the original Mayer–Vietoris complex. The proof of 22.2 invokes simultaneous triples and filtered local limits. Porism 11.18 uses prime-power field extensions; the subsequent transfer argument combines coprime degrees. Perfection is not a hypothesis of this route.

The simultaneous compatibility asserted in the proof of 22.2 must be expanded in Lean. Two independent existence statements for triples do not supply a common base or an extension of the original map.

Do not substitute rational points or separable closed-point residue fields. Smooth affine schemes over imperfect fields can have inseparable closed-point residue fields. Existing coordinate selection and rank arguments use the actual residue extensions and do not need such a substitution. Any geometric Bertini supplier must preserve that scope.

## 5. Candidate shorter route: retain only the needed critical-locus control

A possible alternative to formalizing full whole-fiber Bertini is:

- Start with the checked finite ambient chart θ, étale at selected points.
- Include its non-étale locus and the original missing-neighborhood image in the closed set on which the final base projection is made finite.
- Remove the non-étale locus. The retained curves are then automatically smooth over the same base, while this newly removed boundary is finite.
- Ensure the selected base points avoid the image of the intersection of the removed locus with the required Z. This keeps the full retained Z closed and disjoint from infinity after shrinking the base.

This is only a candidate. A real separation/avoidance theorem is still required. In particular, θ may already identify a selected point with a different non-étale point of Z. No later projection using only θ's coordinates can separate them. One must either impose this finite-fiber separation simultaneously in the initial projection, or return to richer original generators and preserve the relevant constraints during elimination. The existing determinant-avoidance lemmas do not prove this global closed-set avoidance.

The exact decision gate is therefore: prove point-versus-bad-closed-set separation compatible with finite projection and prescribed derivatives, or follow the primary quadratic-embedding/Bertini incidence proof. Do not invest further in generic wrappers until this choice is resolved.

## 6. False shortcuts and counterexamples

- Zariski neighborhoods are not cofinal among étale neighborhoods of zero: an étale square-root neighborhood of `1+t` illustrates the failure. Sheaf excision does not repair representative surjectivity automatically.
- Arbitrary zero-neighborhoods have no monic refinement over the unchanged base: `D(1+s t)` is the relevant relative obstruction. The existing Zariski lifting already avoids this error.
- A finite normalization over the original `P¹_S₀` may have vertical missing boundary. The connected degree-drop family `y²=1+s t`, near `y=1` with 2 invertible, has coordinate `v=t/(y+1)` and `t=v(2+s v)`. Its good `P¹_v` map to `P¹_t` has a basepoint at infinity over s=0. Resolving can add a whole vertical component. Removing a globally disjoint component does not solve this example.
- An actual étale chart at chosen points is not whole-fiber smoothness. Generic finite coordinates and local smooth coordinates cannot be chosen independently and then silently identified.
- Field-only H¹(A¹,F)=0 does not imply arbitrary-base purity, boundary quotient excision, or strict A¹ invariance.

## 7. Bounded parallel work after the roadmap decision

A. Projection geometry: settle the separation/incidence theorem above, including arbitrary residue fields and the literal original map. Output actual compatible compactified curves, not a structure assuming them.

B. Normalization bridge: derive actual generic finite étale maps, specialize the checked normal-source extension, and prove full-boundary finiteness from the finite affine chart and original missing image. This can proceed independently once A fixes the precise retained-open contract.

C. Generic correspondence consumer: complete common-base frame restriction and the already constructed relative Serre/pencil/signed endpoint join. No replacement of supplied geometry by an assumed homotopy.

D. Sheaf comparison: consume genuine local Mayer–Vietoris representative surjectivity plus checked relation reflection to prove local bijectivity of the actual inverse-image canonical map. Then use already checked actual étale sheaf excision and adapted Cartier coordinates for the codimension-one result.

E. Finite fields: after an infinite-field geometric parameter space is explicit, prove existence over sufficiently large prime-power extensions, descend a common original-base neighborhood, push forward the actual correspondence identities using trace, and combine two coprime degrees by an integral Bézout identity. No rational coefficients, silent perfectness strengthening, or assumed transfer descent.
