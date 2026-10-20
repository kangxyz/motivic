# General topological candidates

These leaves extend native topological objects and use no motivic application
prerequisites.

| Exact import | Interface and conditions |
| --- | --- |
| `Motivic.Aglib.Topology.JacobsonOpenCover` | In a Jacobson space, an open containing all closed points is top; any family of open neighborhoods covering the closed points covers every point. The family index has an independent universe. |
| `Motivic.Aglib.Topology.GenericComponentOpens` | In a Noetherian space, remove the other irreducible components while retaining the chosen generic point; in a `T0Space`, the resulting generic-component opens are pairwise disjoint. |

The Jacobson results are
`TopologicalSpace.Opens.eq_top_of_closedPoints_subset` and
`iSup_eq_top_of_closedPoint_neighborhoods`. They assert an actual open cover;
they do not supply presheaf gluing or separatedness. Scheme-neighborhood and
local-zero consumers use this cover before adding their own sheaf hypotheses.
The component-open declarations are `TopologicalSpace.genericComponentOpen`,
`mem_genericComponentOpen` and `genericComponentOpen_pairwiseDisjoint`; the last
retains its `T0Space` premise. No scheme structure is discarded when these
actual opens are used geometrically.
Reuse Mathlib's actual Jacobson and open-set objects. Follow the
[candidate policy](../README.md).
