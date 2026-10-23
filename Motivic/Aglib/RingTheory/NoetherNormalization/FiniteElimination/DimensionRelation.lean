/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.NoetherNormalization.FiniteElimination.Parameterized
public import Mathlib.RingTheory.AlgebraicIndependent.Basic

/-! # Nonzero elimination relations from the actual transcendence-degree bound -/
@[expose] public noncomputable section
open _root_.MvPolynomial
universe u
namespace ParameterizedNoetherNormalization

/-- Excess coordinates have a genuine nonzero relation in the kernel of the
original algebra map. The relation is derived, not supplied to the induction. -/
theorem exists_nonzero_kernel_relation_of_trdeg_le
    {k B : Type u} [Field k] [CommRing B] [Algebra k B] {n d : ℕ}
    (q : MvPolynomial (Fin n) k →ₐ[k] B)
    (hd : Algebra.trdeg k B ≤ d) (hn : d < n) :
    ∃ f : MvPolynomial (Fin n) k, f ≠ 0 ∧ f ∈ RingHom.ker q := by
  have hker : RingHom.ker q ≠ ⊥ := by
    intro heq
    have hq : Function.Injective q := (RingHom.injective_iff_ker_eq_bot q).mpr heq
    have hi : AlgebraicIndependent k (fun i => q (X i)) := by
      apply algebraicIndependent_iff_injective_aeval.mpr
      change Function.Injective (MvPolynomial.aeval (q ∘ X) : _ →ₐ[k] B)
      rw [← MvPolynomial.aeval_unique q]
      exact hq
    have hcard : (n : Cardinal.{u}) ≤ Algebra.trdeg k B := by
      simpa using hi.lift_cardinalMk_le_trdeg
    have hnd : n ≤ d := by exact_mod_cast hcard.trans hd
    exact (Nat.not_le.mpr hn) hnd
  obtain ⟨f, hf, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨f, hne, hf⟩

end ParameterizedNoetherNormalization
