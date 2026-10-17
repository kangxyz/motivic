module
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.MvPolynomial.Ideal

/-! # The native normalization substitution preserves centered first jets

The actual Nagata substitution used by Noether normalization is the identity
modulo the square of the coordinate-origin ideal.  This is a first-order
compatibility fact, not a claim that arbitrary normalization is étale.
-/
@[expose] public noncomputable section
universe u
namespace NoetherNormalization
open MvPolynomial
variable {k : Type u} [Field k] {n : ℕ}

/-- The native substitution fixes first jets along every closed subscheme on
which the eliminated coordinate vanishes, without any residue-field hypothesis. -/
theorem T1_closedBoundaryJets (f : MvPolynomial (Fin (n + 1)) k) (c : k)
    (J : Ideal (MvPolynomial (Fin (n + 1)) k))
    (hJ : X (0 : Fin (n + 1)) ∈ J) :
    (Ideal.Quotient.mkₐ k (J ^ 2)).comp (T1 f c) =
      Ideal.Quotient.mkₐ k (J ^ 2) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, T1, aeval_X]
  split_ifs with hi
  · subst i; rfl
  · have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
    have hexp : 2 ≤ (2 + f.totalDegree) ^ i.val :=
      (by omega : 2 ≤ 2 + f.totalDegree).trans (Nat.le_self_pow hi0 _)
    have hp : (X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) k) ^
        (2 + f.totalDegree) ^ i.val ∈ J ^ 2 :=
      Ideal.pow_le_pow_right hexp (Ideal.pow_mem_pow hJ _)
    have hz : (Ideal.Quotient.mkₐ k (J ^ 2))
        ((X (0 : Fin (n + 1))) ^ (2 + f.totalDegree) ^ i.val) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hp
    rw [map_add, map_smul, hz, smul_zero, add_zero]

/-- The native triangular normalization change fixes the full first infinitesimal
neighborhood of the coordinate origin, for every value of its coefficient. -/
theorem T1_firstJets (f : MvPolynomial (Fin (n + 1)) k) (c : k) :
    (Ideal.Quotient.mkₐ k ((idealOfVars (Fin (n + 1)) k) ^ 2)).comp (T1 f c) =
      Ideal.Quotient.mkₐ k ((idealOfVars (Fin (n + 1)) k) ^ 2) :=
  T1_closedBoundaryJets f c (idealOfVars (Fin (n + 1)) k)
    (Ideal.subset_span ⟨0, rfl⟩)

end NoetherNormalization
