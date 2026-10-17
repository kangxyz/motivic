# Finite-variable polynomial integral closedness

`IsIntegrallyClosed.lean` is the local candidate for
`Aglib.RingTheory.MvPolynomial.IsIntegrallyClosed`. Its native theorem
`MvPolynomial.isIntegrallyClosed_fin` proves integral closedness of
`MvPolynomial (Fin n) R` for every natural number `n`, assuming that the
commutative coefficient ring is a domain and is integrally closed. Its ring
universe is unrestricted; no Noetherianity or characteristic condition is added.

The proof is the original induction using `MvPolynomial.isEmptyRingEquiv`
and `MvPolynomial.finSuccEquiv`. The only import is
`Mathlib.RingTheory.Polynomial.IsIntegral`, whose univariate integral-closedness
instance supplies the induction step. No corresponding finite multivariate
integral-closedness theorem was found in the pinned Mathlib or Aglib sources.

The actual consumers are `Motivic.Aglib.RingTheory.Ideal.GoingDown.Polynomial`
and `Motivic.RingTheory.Smooth.Normal`. The latter imports this focused leaf
without acquiring integral-extension going down. `MotivicTest.GoingDownBaseChange`
checks the independent normality interface and its going-down consequences.
The candidate has no ordinary Motivic application dependency.

The theorem is extracted from `Motivic/RingTheory/GoingDown/Polynomial.lean`,
SHA-256 `45bcfecc8de5aff09198f68b09c269c4ff45a4a2e380c83f0a29fbc1b98939d1`.
The original copyright, license and attribution are retained. Only its native
name and module placement change; the original normal-domain premises and
actual polynomial ring equivalences remain unchanged. Local placement does
not assert upstream acceptance.
