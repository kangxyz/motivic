module
import Motivic.Aglib.RingTheory.NoetherNormalization.Differential.Coordinates
import Mathlib.RingTheory.Derivation.Basic

/-! # Actual residue-field derivations and the finite-coordinate selection -/
open _root_.MvPolynomial ParameterizedNoetherNormalization

example {k : Type} [Field k] [Infinite k] {n d : ℕ}
    (f : MvPolynomial (Fin (n + 1)) k)
    (I : Ideal (MvPolynomial (Fin (n + 1)) k)) (hf : f ≠ 0) (hIf : f ∈ I)
    {ι : Type} [Finite ι] (K : ι → Type)
    [∀ i, Field (K i)] [∀ i, Algebra k (K i)]
    [∀ i, Module (MvPolynomial (Fin (n + 1)) k) (K i)]
    (D : (i : ι) → Fin d → Derivation k (MvPolynomial (Fin (n + 1)) k) (K i))
    (j : ι → Fin d → Fin n)
    (hD : ∀ i, Matrix.det (fun a b => D i a (X (j i b).succ)) ≠ 0) :
    ∃ c : k, c ≠ 0 ∧
      ((Ideal.Quotient.mkₐ k I).comp
        ((coordinateChange f c).symm.toAlgHom.comp (MvPolynomial.rename Fin.succ))).Finite ∧
      ∀ i, Matrix.det
        (fun a b => D i a ((coordinateChange f c).symm (X (j i b).succ))) ≠ 0 :=
  exists_finite_projection_preserving_differential_minors f I hf hIf K
    (fun i a => (D i a).toLinearMap) j hD
