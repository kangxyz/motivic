# Singular complexes with transfers

This family constructs the original parameter singular complex of an additive
presheaf with transfers and then its transfer-preserving sheafification. It
retains actual simplex pullbacks, alternating differentials and graph actions.

| Exact import | Interface |
| --- | --- |
| `Motivic.Transfers.SingularComplex.Presheaf` | Singular complex of the actual transfer presheaf |
| `Motivic.Transfers.SingularComplex.Sheafification` | The actual sheafified singular complex |

The algebraic-simplex coordinate ring has the
[general ring-theory owner](../../Aglib/RingTheory/AlgebraicSimplex/README.md);
its geometric realization and products use the same object and original maps.
The [presheaf family](../Presheaf/README.md) supplies the transfer action and
reduced-torus coefficients. The current motivic model shifts that singular
complex so chain degree `r` in weight `q` occupies cochain degree `q-r`, with
the original differential and shift signs. See
[Suslin–Voevodsky cohomology](../../Cohomology/SuslinVoevodsky/README.md).

Use exact lower leaves for implementation work. This construction does not
supply a higher-Chow, motives or spectrum comparison, nor general
HI-presheaf sheafification. Model comparisons retain separate maps and proofs.
