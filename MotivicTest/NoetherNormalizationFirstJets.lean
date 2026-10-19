module
import Motivic.Aglib.RingTheory.NoetherNormalization.FirstJets
/-! # Direct first-order audit of the actual native normalization substitution -/
open _root_.MvPolynomial

example {k : Type} [Field k] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) k) (c : k) :
    (Ideal.Quotient.mkₐ k ((idealOfVars (Fin (n + 1)) k) ^ 2)).comp
        (NoetherNormalization.T1 f c) =
      Ideal.Quotient.mkₐ k ((idealOfVars (Fin (n + 1)) k) ^ 2) :=
  NoetherNormalization.T1_firstJets f c
