module
import Motivic.Aglib.RingTheory.Bertini.IncidenceNonDominance
import Lean.Util.CollectAxioms

/-! # A literal equation for the full, possibly nonreduced incidence image -/
open Algebra

example (k B : Type) [Field k] [CommRing B] [Algebra k B] (n : ℕ)
    (f : MvPolynomial (Fin (n + 1)) k →ₐ[k] B)
    (h : ∀ P ∈ minimalPrimes B, trdeg k (B ⧸ P) ≤ (n : Cardinal)) :
    ∃ p : MvPolynomial (Fin (n + 1)) k, p ≠ 0 ∧ f p = 0 := by
  apply exists_nonzero_kernel_of_minimal_quotient_trdeg_lt f
  intro P hP
  simp only [MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fin, Cardinal.lift_natCast]
  exact lt_of_le_of_lt (h P hP) (by exact_mod_cast Nat.lt_succ_self n)

open Lean in
run_cmd do
  for name in #[``not_injective_of_minimal_quotient_trdeg_lt,
      ``exists_nonzero_kernel_of_minimal_quotient_trdeg_lt] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Incidence non-dominance: standard foundations only."
