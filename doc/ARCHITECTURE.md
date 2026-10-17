# Architecture

## Objects and implementation ownership

Motivic is a reusable mathematics library. Its present model constructs
motivic cohomology from actual finite correspondences and the sheafified
Suslin complex of the reduced torus. Alternative models must be connected by
explicit comparison maps and theorems. They do not silently replace this model.

Reuse the pinned Mathlib object first, then its Aglib extension. There is one
canonical implementation of each object and map. Compatibility leaves import
or identify that implementation rather than constructing a parallel copy.
A native declaration namespace names the mathematical object; the `Motivic`
module prefix identifies where its source is maintained.

## Source families

| Owner | Responsibility |
| --- | --- |
| `Motivic/Algebra`, `Motivic/RingTheory` | Local algebraic/homological foundations used by geometry and cohomology |
| `Motivic/Aglib` | Inherited candidates for future upstream contribution; currently a local staging area |
| `Motivic/AlgebraicGeometry` | Smooth sites, actual correspondences, products and presheaves with transfers |
| `Motivic/Transfers` | Additive transfer sheaves, exactness, injectives and ordinary-cohomology transfers |
| `Motivic/Cohomology` | Ordinary sheaf cohomology, relative cohomology and hypercohomology |
| `Motivic/Cohomology/Motivic` | Canonical motivic complexes, coefficients, field change and computations |
| `Motivic/KTheory` | Milnor quotients, residues, norms and their comparison inputs |
| `MotivicTest` | Focused interface consumers and inherited proof/trust checks |
| `examples/downstream` | A separate client package exercising public imports |
| `doc/provenance` | Immutable imported source/evidence records, outside the build graph |

The existing local Aglib candidates include imports back into Motivic
geometry/cohomology. Their directory name is not proof of a standalone upstream
boundary. Before promotion, split generic primitives from applications, inspect
actual imports, reconcile native owners, and update affected consumers. Do not
create a root `Aglib/` subtree or shadow the upstream package.

## Dependency and public API boundaries

Keep the actual import graph acyclic. General ring/category/complex primitives
should lie below their geometric uses. Geometric correspondences precede
transfer presheaves; transfer exactness and ordinary cohomology feed the
all-degree transfer comparison. Motivic complexes and Milnor groups are
independently defined; comparison modules consume both sides. Applications
consume these constructions and cannot be prerequisites for their definitions.

Each family facade reexports a deliberately selected interface. Production
leaves import lower leaves, not a package/family facade to obtain one helper.
`Motivic.lean` selects four core entries. Characteristic-zero Milnor norm, diagonal and weight-one computation
entries are optional; no generated catch-all root admits every retained leaf.
Historical missing logs are evidence gaps, not proof failures or permissions
to strengthen statements. New admissions need the actual affected compilation
and statement/map correspondence.

Keep tests, clients, historical documents and scratch outside production
imports. Selective independent checks can inspect private/generated names,
but an audit import does not become the public mathematical interface.

## Growth

Extend a current family when its actual object fits. New motives, stable
homotopy, etale or higher-Chow objects need their own occupied families and
explicit comparison modules when implemented. Preserve the smooth-field
construction and its scope while introducing broader bases or coefficients;
do not hide changed theories behind an existing name. No empty future source
trees or general framework is required in advance.
