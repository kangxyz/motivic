# General finite-extension candidates

This occupied family extends actual field extensions and polynomial witnesses.
Use the exact lower import for its displayed field, degree, coprimality and
avoidance hypotheses. These are general interfaces; motivic specialization
stays outside the candidate closure.

| Exact import | Interface and boundary |
| --- | --- |
| `Motivic.Aglib.FieldTheory.FiniteExtension.Avoidance.Polynomial` | Retains the original finite-extension objects, polynomial witnesses and displayed hypotheses. |
| `Motivic.Aglib.FieldTheory.FiniteExtension.Avoidance.ResiduePolynomial` | Retains the original finite-extension objects, polynomial witnesses and displayed hypotheses. |
| `Motivic.Aglib.FieldTheory.FiniteExtension.Avoidance.WholeFiber` | Retains the original finite-extension objects, polynomial witnesses and displayed hypotheses. |
| `Motivic.Aglib.FieldTheory.FiniteExtension.CoprimeTensorField` | Retains the original finite-extension objects, polynomial witnesses and displayed hypotheses. |
| `Motivic.Aglib.FieldTheory.FiniteExtension.PrimeDegrees` | Retains the original finite-extension objects, polynomial witnesses and displayed hypotheses. |

Already accepted Sylow fixed-field, rational-function and Milnor interfaces use
pinned Aglib directly. A statement for an explicitly supplied finite polynomial
family is not a global p-special closure or a degree-gap assertion for every
polynomial over an extension. Current consumers are general scalar-extension
and geometric parameter constructions. See the [candidate policy](../README.md).
