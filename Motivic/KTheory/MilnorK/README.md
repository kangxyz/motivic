# Integral Milnor groups in every degree

`Basic` defines `Motivic.KTheory.MilnorK.K F n` as a genuine quotient of the
free abelian group on `Fin n → Fˣ`. Relations are multiplication in each
coordinate and the adjacent Steinberg relations. `lift` is its universal
extension to an arbitrary abelian target; it is not a hypothesis on the group.

`Map` gives the actual functorial maps for field homomorphisms, allowing
independent source and target universes. `LowDegree` proves the canonical
identifications in degrees zero and one with `ℤ` and `Additive Fˣ`.

`CompatibilityK2` and `CompatibilityK3` give mutually inverse symbol-preserving
maps to the earlier tensor presentations, including their actual field maps.
This allows existing low-degree results to be reused without redefining them.

`Product` constructs the actual concatenation product by descending both
quotient factors. Its symbol formula, arbitrary-field naturality, empty-symbol
unit laws, integer degree-zero action, and associativity hold for arbitrary
nonnegative degrees. `degreeCongr` explicitly handles equality of degrees and
reindexes symbols by `Fin.cast`; associativity uses the actual tuple
reassociation. The two generic tuple-update lemmas live in namespace `Fin`.

`Symbols` inserts an adjacent pair through the existing actual K₂ quotient,
retaining every other coordinate. This transports the proved `(a,-a)`
vanishing, `(a,a) = (a,-1)` identity, and adjacent skew symmetry to every
degree. It does not assume alternation or characteristic zero.

The family facade is [Motivic.KTheory.MilnorK](../MilnorK.lean). Exact
consumer modules under `MotivicTest` can be selected using the guarded
`python3 scripts/build.py MODULE` route from the repository root; see
[development](../../../doc/DEVELOPMENT.md). Some inherited consumers deliberately
use legacy imports to inspect private/generated declarations; their exact module
is the acceptance target rather than an import into a new public module.

## Residues, specialization and norms

`ResidueSpecialization` constructs all-degree specialization from actual DVR
valuation and residue data, including unit-part twists and the degree-two
comparison. Specialization depends on a uniformizer. `Residue`,
`ResidueCompatibility` and `ResidueDVR` construct tame residues, compare the
previous K2/K3 maps, and retain their complete normalization and valuation
hypotheses. Tame-residue uniformizer independence is a separate theorem from
specialization.

`PolynomialNorm` supplies presentation-based polynomial norms. The later
`FiniteExtensionNorm` family constructs finite-extension norms in characteristic
zero; `FiniteExtensionNormTower` supplies their transitivity with explicit
finite-dimensional, algebra and tower data. The optional `Motivic.KTheory.MilnorK.Norms` facade exports that endpoint.
Use the optional [Norms](Norms.lean) entry to import this characteristic-zero
family; the all-field core entry keeps symbol quotients, products and residues
independent of it. This is separate from an assertion of a positive-characteristic norm/diagonal
comparison or unrestricted curve reciprocity. Read each exact declaration for
its base-field, coefficient and universe assumptions.

The optional motivic comparison entry is
[Motivic.Cohomology.Motivic.Diagonal](../../Cohomology/Motivic/Diagonal.lean).
Milnor groups are independently defined symbol quotients; the comparison uses
the original motivic group and maps, with its characteristic-zero and
cohomological hypotheses. Strict A1 invariance remains open.

[Historical check evidence](../../../doc/provenance/README.md) identifies the
exact imported source hashes and successful Linux consumers. It does not
certify renamed tests or assert a fresh whole-library build.
