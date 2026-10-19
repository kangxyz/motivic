module
import Motivic.Aglib.RingTheory.NoetherNormalization.FiniteElimination.Parameterized
import Motivic.Aglib.RingTheory.Polynomial.Avoidance.SimultaneousResidue
/-! # Direct finite-coordinate and residue-selection consumers -/
open _root_.MvPolynomial ParameterizedNoetherNormalization

example {k : Type} [Field k] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) k)
    (I : Ideal (MvPolynomial (Fin (n + 1)) k))
    (c : k) (hc : c ≠ 0) (hf : f ≠ 0) (hIf : f ∈ I) :
    ((Ideal.Quotient.mkₐ k I).comp
      ((coordinateChange f c).symm.toAlgHom.comp (MvPolynomial.rename Fin.succ))).Finite :=
  coordinateChange_finite_projection f I c hc hf hIf

example (k : Type) [Field k] [Infinite k] {ι : Type} [Finite ι]
    (K : ι → Type) [∀ i, Field (K i)] [∀ i, Algebra k (K i)]
    (p : (i : ι) → Polynomial (K i)) (hp : ∀ i, (p i).eval 0 ≠ 0) :
    ∃ c : k, c ≠ 0 ∧ ∀ i, (p i).eval (algebraMap k (K i) c) ≠ 0 :=
  Polynomial.exists_nonzero_scalar_preserving_residue_conditions k K p hp
