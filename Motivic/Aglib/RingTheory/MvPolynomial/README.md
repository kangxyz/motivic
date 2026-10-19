# Finite-variable polynomial integral closedness

`Motivic.Aglib.RingTheory.MvPolynomial.IsIntegrallyClosed` is the local source owner.
A future upstream contribution is separate from its present reusable interface. Its native theorem
`MvPolynomial.isIntegrallyClosed_fin` proves integral closedness of
`MvPolynomial (Fin n) R` for every natural number `n`, assuming that the
commutative coefficient ring is a domain and is integrally closed. Its ring
universe is unrestricted; no Noetherianity or characteristic condition is added.

The proof is the original induction using `MvPolynomial.isEmptyRingEquiv`
and `MvPolynomial.finSuccEquiv`. The only import is
`Mathlib.RingTheory.Polynomial.IsIntegral`, whose univariate integral-closedness
instance supplies the induction step.

The actual consumers are `Motivic.Aglib.RingTheory.Ideal.GoingDown.Polynomial`
and `Motivic.Aglib.RingTheory.Smooth.Normal`. The latter imports this focused leaf
without acquiring integral-extension going down. `MotivicTest.GoingDownBaseChange`
checks the independent normality interface and its going-down consequences.
The local leaf has no ordinary Motivic application dependency.
