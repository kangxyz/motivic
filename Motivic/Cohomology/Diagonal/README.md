# Diagonal motivic cohomology

| Exact import | Interface |
| --- | --- |
| `Motivic.Cohomology.Diagonal` | Focused characteristic-zero diagonal entry |
| `Motivic.Cohomology.Diagonal.MilnorEquivalence` | Original Milnor symbol equivalence |
| `Motivic.Cohomology.Diagonal.MilnorEquivalenceNaturality` | Actual field-map naturality |

For `k : Type u`, `[Field k]`, `[CharZero k]` and `q : ℕ`, the equivalence
`Motivic.DiagonalMilnorEquivalence.motivicEquiv` compares `MilnorK.K k q` with
the original group `Motivic.motivicCohomology k q q (SmoothSite.base (Spec (.of k)))`.
The smooth-site argument is the base object `Spec k`. Ordinary
`HasDerivedCategory.{w}` for Nisnevich sheaves valued in `AddCommGrpCat.{u + 1}`
remains explicit. The comparison
consumes the current [Suslin–Voevodsky model](../SuslinVoevodsky/README.md)
and independent Aglib's `MilnorK.K k q`; it does not define either object.

Preserve the actual symbol map, field maps and their naturality.
`MotivicTest.DiagonalMilnorEquivalenceNaturality` is an existing consumer of
these original interfaces. Low-degree tensor presentations use Aglib's
explicit equivalences with `MilnorK.K`; they are not another general theory.

Positive-characteristic diagonal comparison remains a separate obligation.
This computation does not supply a higher-Chow, motives or spectrum comparison.
Use precise lower leaves and retain each theorem's full field, degree,
universe and derived-category conditions.
