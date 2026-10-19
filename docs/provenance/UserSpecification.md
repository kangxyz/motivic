# Motivic cohomology library implementation plan

This plan serves B10 in the [background programme](ROADMAP.md#background-establishment-programme).
The source basis is commit `1e2b2a1a27c19ecbb9575ef9eeb57d0ae46f520e` with
Lean 4.34.1, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` and
Quillen `e041130406653095d0701f5f08783d796bd0317c`. These are planned
implementations, not newly proved results or an exposé-status assignment.

## Objective and first scope

Build a reusable library whose motivic complexes, maps and coefficients are
actual constructions. Supply the theorem terms currently retained by the
elliptic K2 source comparison. The initial proof scope is characteristic-zero
fields, weights one and two, every positive coefficient level, and arbitrary
field homomorphisms, including extensions to completion fraction fields.
Define the underlying complexes in every simplicial degree; general weights
can have definitions before their computation/comparison theorems are proved.

The current arithmetic model is handled by native etale H1. Motivic evaluation
on a mixed-characteristic arithmetic surface is not an initial requirement.
An extension to singular or mixed-characteristic bases will need its own
definition and comparison scope.

## Canonical definition

Use the Suslin--Voevodsky finite-correspondence model. For a perfect field k,
let Cor(k) be the category of smooth separated finite-type k-schemes and
finite correspondences. Construct the presheaf with transfers
Z_tr(G_m^{wedge q}), with the identity-axis quotient defined geometrically.
Set

```text
C_r(P)(U) = P(U x Delta^r)
Z(q) = a_Nis(C_*(Z_tr(G_m^{wedge q})))[-q]
H^{p,q}(X,Z) = hypercohomology_Nis^p(X,Z(q)).
```

Place C_r in cochain degree q-r. Thus chain degrees 1/0 in weight two give
cohomological degrees 1/2. The current Grayson/cycle low-degree conventions
must be compared to this placement explicitly.

Sources: MVW, Definition 3.1, Example 13.11 and Proposition 14.16,
[author manuscript](https://sites.math.rutgers.edu/~weibel/MVWnotes/xprova.pdf).
The book initially uses Zariski hypercohomology. The library's Nisnevich
interface requires a proved Zariski/Nisnevich comparison at the stated scope.

### Other models and extension boundaries

| Model | Role and required bridge |
| --- | --- |
| Bloch higher Chow complex | Computation/comparison backend. Its term is z^q(-,2q-i) in cochain degree i. In weight two H1/H2 use chain degrees 3/2. Prove a natural derived comparison, including products and coefficients; do not relabel existing terms. |
| DM effective motives | Later representability interface for smooth perfect-field schemes. Prove the Hom/hypercohomology identification; it is not the first implementation prerequisite. |
| Motivic Eilenberg--MacLane spectrum MZ | Later stable presentation, requiring its own spectrum construction and comparison. The current low-weight field consumer does not require the entire stable motivic category. |
| General singular/arithmetic theories | Separate extension decision. Their smooth-field agreement does not identify all versions on arbitrary bases. |

The smooth-field higher-Chow comparison, including coefficients, is
Voevodsky (2002), *Motivic Cohomology Groups Are Isomorphic to Higher Chow
Groups in Any Characteristic*, Theorem 1 and Corollary 2,
[published paper](https://www.math.ias.edu/vladimir/sites/math.ias.edu.vladimir/files/motivic_cohomology_groups_are_isomorphic_published.pdf).
For the characteristic-zero spectrum comparison see
[Röndigs--Østvær, Modules over motivic cohomology](https://www.sciencedirect.com/science/article/pii/S0001870808001655).
The distinct general-scheme objectives are illustrated by
[Elmanto--Morrow](https://arxiv.org/abs/2309.08463) and
[Bachmann--Elmanto--Morrow](https://arxiv.org/abs/2508.09915).

## Source ownership and dependency direction

The following paths are proposed ownership boundaries, not empty directories
to create before there is an implementation:

```text
R5Lab/AlgebraicGeometry/Correspondences/     geometric finite correspondences
R5Lab/Cohomology/Motivic/                   canonical complexes and operations
R5Lab/Cohomology/Motivic/EtaleComparison/   finite coefficient comparison
R5Lab/KTheory/Comparisons/Motivic/          Milnor/Grayson/Quillen comparisons
```

The motivic core must not import a selected Grayson ComparisonSystem or an
arithmetic K2 application to define its objects. Comparison modules import
both sides. B06 supplies canonical Milnor norms to the Milnor comparison,
not to the definition of the motivic complex.

Reuse the current geometric generators, simplex rings/faces, local-length
calculations and coefficient-cone algebra after checking their exact scope.
Their current source ownership and accepted statements are preserved until a
reviewed extraction/adapter milestone. Existing bounded transport does not
prove the complete sheaf-level identification.

## Work packages

| Package | Implementation and exact acceptance target | Dependencies |
| --- | --- | --- |
| MC01 Finite correspondences | Define actual cycles finite and surjective over source components, graph correspondences and composition with multiplicities. Prove identity/associativity and graph/base-change laws on smooth schemes. Declare any missing intersection/length lemma as an explicit owned prerequisite. | Existing scheme, finite-morphism and local-length APIs; B01 as needed. |
| MC02 Transfers and sheafification | Construct additive contravariant presheaves on Cor(k), represented transfer presheaves and Nisnevich sheafification with transfers. Prove that the transfer actions and restrictions survive sheafification. | MC01 and existing ordinary sheaf APIs. |
| MC03 Singular and motivic complexes | Construct the full algebraic simplex, all faces/degeneracies, C_*, normalization comparison, reduced torus and the [-q] shift. Prove d squared zero and the exact current low-degree/truncation dictionary. | MC01--MC02 and existing simplex/chain-complex APIs. |
| MC04 Cohomology and field evaluation | Construct the chosen hypercohomology interface and its relationship to complex evaluation. Prove exact Nisnevich evaluation at Spec K using split covering sieves; do not apply that argument to etale evaluation. | MC02--MC03 and the actual derived/sheaf tools. |
| MC05 Coefficients and products | Construct derived finite coefficients, coefficient triangles/Bocksteins, reductions, insertions and shuffle/Koszul products. Prove compatibility with current cone and termwise coefficient models where their hypotheses apply. | MC03--MC04 and existing coefficient-cone computations. |
| MC06 Change of ground field | Construct K-to-L base change between smooth sites for arbitrary field homomorphisms. Prove composition, naturality of products/coefficients and needed filtered-continuity statements. Do not require Spec L to be finite type over K. | MC01--MC05. |
| MC07 Weight-one and integral weight-two computations | Establish the normalized weight-one computation and the point/norm Milnor comparison in weight two, including theta injectivity. Prove correspondence with B06's exact norm family and the current determinant/scalar maps. | MC01--MC06; B06 for the Milnor adapter. |
| MC08 Finite etale comparison | Define the actual change-of-topology/product-induced arrow and prove its comparison in the degree-one weight-two range, plus the needed algebraically closed coefficient/vanishing results. Every additional source-theorem prerequisite must be proved or separately marked open. | MC04--MC07, B02--B03 and etale/Galois coefficient objects. |
| MC09 Actual Grayson adapters | Identify the complete geometric cycle source and prove the Suslin quasi-isomorphism for the actual fullCycleMap. Derive the integral/finite determinant, closedPhi, hzero and signed-arrow theorem terms for current consumers. | MC01--MC08 and the existing Grayson source. |
| MC10 Final instantiation and optional presentations | Populate the existing SourceSystem/fieldSystem and fieldDVRBackground with proved terms; check literal maps and final arithmetic consumers. Higher-Chow, DM and spectrum presentations are distinct later comparisons with their own consumers. | MC09, B06 and the independently proved DVR backgrounds. |

MC01--MC06 are the reusable foundation. MC07--MC09 contain substantial
mathematics; implementing a target record is not a proof of a comparison.
At a mathematical milestone, review the exact source scope and actual maps.
Current Suslin 2003 corrections remain part of that scope. The separate
Suslin 1987 prime-root-symbol issue stays with B12.

## Map and coefficient invariants

Use derived coefficients Z/n(q) = Z(q) tensor^L Z/n, with the triangle
Z(q) --n--> Z(q) --> Z/n(q) --> Z(q)[1]. Preserve the current cone convention
da = n b and beta([(a,b)]) = [b], including the positive coefficient projection.

The required map is

```text
H1(K,Z/n(2)) --beta--> H2(K,Z(2))[n] --theta--> MilnorK2(K)[n].
```

Its kernel before any special arithmetic argument is the image of
H1(K,Z(2))/n. Finite comparison alone does not prove Bockstein injectivity.
Keep the separate prime-symbol and pointed/origin arguments when instantiating
the original arithmetic theorem.

The finite etale coefficient is mu_n tensor mu_n, with diagonal square
cyclotomic action. Do not replace it by a globally trivialized Z/n coefficient.
All positive n are required, including composite n and n=1; level one is a
zero-coefficient case, not a hidden positivity exception. Products, reduction
and insertion must preserve the exact normalizations already consumed by K2.

Every field, including a completion fraction field, is its own ground field.
Field maps compare theories by ground-field base change. This avoids evaluating
a fixed-base finite-type presheaf outside its domain.

## Milestones and verification

1. Freeze definitions, indexing and ownership for MC01--MC06. Resolve concrete
   missing foundation APIs before dispatching dependent proof packages.
2. Build the actual low-weight source and coefficient operations; prove its
   field-evaluation and base-change identities. A record of H1/H2 groups is
   not this milestone.
3. Prove the integral and finite computations with their canonical maps.
   Record remaining source/pretheory/purity/norm-residue obligations rather
   than moving them into new assumptions.
4. Prove the actual Grayson bridge and instantiate the current theorem-valued
   inputs. Reuse FullCycleBridge and accepted coefficient/naturality algebra.
5. Check final field-system premise lists and the real n=1, composite-level
   and completion-field consumers. Preserve same-class restriction and beta;
   do not infer map equality from an abstract group isomorphism.

Authors run exact leaf/consumer builds and repair their own diagnostics.
Use mathematical/source review and selected origin axiom checks/normal replay
at coherent milestones; reuse unchanged results. New proofs start at 200000
heartbeats with only explained finite declaration-local exceptions. No pin
change, broad repeated package build, status assignment or automatic commit
is part of this planning document.
