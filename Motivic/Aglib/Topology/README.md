# General topological candidates

These leaves extend native topological objects and use no motivic application
prerequisites.

| Exact import | Interface and conditions |
| --- | --- |
| `Motivic.Aglib.Topology.JacobsonOpenCover` | In a Jacobson space, an open containing all closed points is top; any family of open neighborhoods covering the closed points covers every point. The family index has an independent universe. |
| `Motivic.Aglib.Topology.GenericComponentOpens` | Generic-component open constructions under the leaf's explicit topological hypotheses |

The Jacobson results are
`TopologicalSpace.Opens.eq_top_of_closedPoints_subset` and
`iSup_eq_top_of_closedPoint_neighborhoods`. They assert an actual open cover;
they do not supply presheaf gluing or separatedness. Scheme-neighborhood and
local-zero consumers use this cover before adding their own sheaf hypotheses.
Reuse Mathlib's actual Jacobson and open-set objects. Follow the
[candidate policy](../README.md).
