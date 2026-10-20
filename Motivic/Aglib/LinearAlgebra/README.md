# General module and determinant candidates

These interfaces retain actual module elements, dual functionals and scalar
maps. They are general linear algebra, with geometry as a consumer.

| Exact import | Interface and full boundary |
| --- | --- |
| `Motivic.Aglib.LinearAlgebra.InvertibleModule.PrescribedTrivialization` | A prescribed unit coordinate of a finite projective rank-one module after a surjective scalar map extends to a principal localization. The scalar restricts to one, and the coordinate agrees with the prescribed map on every original element. |
| `Motivic.Aglib.LinearAlgebra.Dual.ProjectiveBaseChange` | For a finite projective module over a commutative semiring, base changes of its original dual functionals jointly detect zero over every commutative algebra. No flatness, reducedness, field or global-freeness premise is added. |
| `Motivic.Aglib.LinearAlgebra.Determinant.RankOne` | `LinearMap.det_id_add_smulRight` proves `det(id + ell.smulRight v) = 1 + ell v` on the original finite free module over any commutative ring, with no freeness premise on the kernel of `ell`. |

The dual result uses the existing finite-projective contraction equivalence.
Line-bundle frames and actual geometric scalar extensions consume these maps;
they do not replace them with unspecified trivializations. Preserve module and
scalar universes and the surjectivity premise of prescribed trivialization.
The determinant leaf supplies the rank-one update used by the
[marked-fiber norm](../RingTheory/Norm/FiniteFree/MarkedFiber.lean).
Follow the [candidate policy](../README.md).
