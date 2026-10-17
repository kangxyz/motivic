module
import Motivic.Aglib.RingTheory.CenteredNoetherNormalization
/-! # Monic elimination and first jets for the same actual coordinate change -/
open MvPolynomial Polynomial

example {k : Type} [Field k] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) k)
    (I : Ideal (MvPolynomial (Fin (n + 1)) k)) (hf : f ≠ 0) (hIf : f ∈ I) :
    ∃ e : MvPolynomial (Fin (n + 1)) k ≃ₐ[k] MvPolynomial (Fin (n + 1)) k,
      (Ideal.Quotient.mkₐ k ((idealOfVars (Fin (n + 1)) k) ^ 2)).comp e.toAlgHom =
        Ideal.Quotient.mkₐ k ((idealOfVars (Fin (n + 1)) k) ^ 2) ∧
      ∃ g : (MvPolynomial (Fin n) k)[X], g.Monic ∧
        g ∈ (I.map e).map (finSuccEquiv k n) :=
  CenteredNoetherNormalization.exists_coordinateChange_firstJets_monicRelation f I hf hIf
