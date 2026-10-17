module
import Motivic.Aglib.RingTheory.CenteredFiniteElimination
/-! # Finite original-quotient projection with prescribed surviving first jets -/
open MvPolynomial

example {k : Type} [Field k] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) k)
    (I : Ideal (MvPolynomial (Fin (n + 1)) k)) (hf : f ≠ 0) (hIf : f ∈ I) :
    ∃ p : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin (n + 1)) k,
      ((Ideal.Quotient.mkₐ k I).comp p).Finite ∧
      (Ideal.Quotient.mkₐ k ((idealOfVars (Fin (n + 1)) k) ^ 2)).comp p =
        (Ideal.Quotient.mkₐ k ((idealOfVars (Fin (n + 1)) k) ^ 2)).comp
          (MvPolynomial.rename Fin.succ) :=
  CenteredNoetherNormalization.exists_finite_projection_preserving_surviving_jets f I hf hIf

example {k : Type} [Field k] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) k)
    (I J : Ideal (MvPolynomial (Fin (n + 1)) k)) (hf : f ≠ 0) (hIf : f ∈ I)
    (hJ : X (0 : Fin (n + 1)) ∈ J) :
    ∃ p : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin (n + 1)) k,
      ((Ideal.Quotient.mkₐ k I).comp p).Finite ∧
      (Ideal.Quotient.mkₐ k (J ^ 2)).comp p =
        (Ideal.Quotient.mkₐ k (J ^ 2)).comp (MvPolynomial.rename Fin.succ) :=
  CenteredNoetherNormalization.exists_finite_projection_preserving_closedBoundary_jets
    f I J hf hIf hJ
