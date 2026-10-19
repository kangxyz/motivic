# General ring-theory candidates

These candidates extend actual rings, ideals, localizations and modules. Use
native namespaces and the pinned Mathlib/Aglib object before adding source.
Preserve actual algebra maps, quotient ideals, nilpotents and infinite-valued
lengths; conversion to a natural length retains its finiteness proof.

| Exact import | Interface and boundary |
| --- | --- |
| `Motivic.Aglib.RingTheory.Ideal.GoingDown.BaseChange` | Going down for actual finite-type tensor base change, retaining integral/faithful/domain-target/normal-base hypotheses. |
| `Motivic.Aglib.RingTheory.MvPolynomial.IsIntegrallyClosed` | Finite-variable polynomial integral closedness over an integrally closed domain. |
| `Motivic.Aglib.RingTheory.Spectrum.Prime.FlatScalarMinimalPrimes` | Generic components under the stated flat/torsion-free scalar maps. |
| `Motivic.Aglib.RingTheory.Multiplicity.Cartier.CutLength` | Regular singleton Koszul Euler characteristic and actual finite quotient length, retaining scalar transport. |
| `Motivic.Aglib.RingTheory.AlgebraicSimplex.Basic` | Actual polynomial quotient defining the algebraic-simplex coordinate ring. |
| `Motivic.Aglib.RingTheory.Norm.FiniteFree.MarkedFiber` | Marked scalar/residual-one norm under actual split base change; the original algebra remains finite free, without separate residual finiteness or freeness. |

See [going down](Ideal/GoingDown/README.md),
[polynomial normality](MvPolynomial/README.md) and
[algebraic-simplex rings](AlgebraicSimplex/README.md). General finite-extension,
Bertini, differential and norm prerequisites use their exact lower leaves;
geometric scalar-extension specializations have their general geometry owner
before candidate algebra consumes them. No host application dependency is waived.

Current consumers include general smooth normality and actual finite geometric
base changes, followed by host correspondence and invariance proofs. Already
accepted field theory, Milnor theory and norm interfaces are imported from Aglib.
[Six host local-length adapters](../../RingTheory/README.md) preserve their
existing native aliases rather than supplying another implementation.
