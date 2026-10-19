# Naming conventions

## Imports and native owners

The package and production import root are `Motivic`; tests use `MotivicTest`.
A module path identifies source ownership, while declaration namespaces follow
the actual mathematical object. General candidates use the temporary import
prefix `Motivic.Aglib`, with native namespaces such as `CategoryTheory`,
`AlgebraicGeometry.Scheme`, `CochainComplex` and `Ideal`. Never create a
package-root `Aglib/` tree that shadows the upstream dependency.

Host constructions retain their mathematical names. Moving a general source
into the candidate tree normally changes imports rather than declarations.
Already available Mathlib/Aglib APIs retain their canonical names and maps.
Close the enclosing namespace and reopen the intended native namespace instead
of using `namespace _root_` or `namespace _root_.…`, which create literal
namespace components.
The [interface index](INTERFACES.md) routes to exact objects, namespace exceptions
and comparisons; detailed definitions belong in those family guides.

## Parent context and leaves

Use PascalCase module components and Mathlib declaration conventions. Shorten
a leaf only when the parent fixes the same object. `Basic`, `Comparison`,
`Unit` and `Naturality` need a precise parent and a family guide. Keep complete
object names when shortening changes their meaning. Field branches distinguish
the actual field conditions.

Name leaves by mathematical objects, properties and comparisons, avoiding
proof attempts, migration lanes and future milestones. Group general geometry
by its scheme, morphism, module, site or cycle object. Neither a theorem's name
nor its motivating application selects source ownership.

Use native `map`, `map_id`, `map_comp`, `...Iso` and appropriate `...Equiv`
conventions. Preserve original graph, restriction, boundary, norm and coefficient
maps in comparison names. Do not add aliases solely for a package prefix.

## Facades and documentation

A facade contains precise public imports and a scope comment. Implementation
leaves import exact lower leaves. Add a facade only for an actual consumer;
keep the four curated root entries small. Current imports are listed in the
[library guide](../Motivic/README.md).

Family guides own definitions, complete hypotheses, universes, degree/sign
conventions, API examples, current consumers and remaining theorem inputs.
Central `docs/` pages summarize conventions and link to those owners. Preserve
historical names at their identified provenance locators rather than presenting
them as current imports. See [architecture](ARCHITECTURE.md).
