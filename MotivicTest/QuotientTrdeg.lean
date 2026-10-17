module
public import Motivic.Aglib.RingTheory.AlgebraicIndependent.QuotientTrdeg
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Lean.Util.CollectAxioms

/-! # Nonreduced quotient transcendence-degree regression tests -/
@[expose] public noncomputable section

open Polynomial

namespace Motivic.MotivicTest.QuotientTrdeg

universe u v w z

/-- The ambient dimension bound, not a supplied bound on the quotient, is used. -/
theorem actual_quotient_dimension_drop
    {k R : Type u} [Field k] [CommRing R] [IsDomain R] [Algebra k R]
    (I : Ideal R) (hI : I ≠ ⊥) {d : ℕ}
    (hd : Algebra.trdeg k R ≤ (d : Cardinal.{u}) + 1) :
    Algebra.trdeg k (R ⧸ I) ≤ d :=
  I.trdeg_quotient_le_of_ne_bot hI hd

/-- Appending a regular kernel element does not assume the target is a domain. -/
theorem regular_kernel_extends_family
    {k : Type u} {R : Type v} {S : Type w} {ι : Type z}
    [CommRing k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (f : R →ₐ[k] S) {x : ι → R} (hx : AlgebraicIndependent k (f ∘ x))
    {t : R} (ht : t ∈ nonZeroDivisors R) (hft : f t = 0) :
    AlgebraicIndependent k (fun o : Option ι => o.elim t x) :=
  hx.option_of_comp_of_regular_ker f ht hft

/-- The literal double-point quotient has transcendence degree zero. -/
theorem double_point_trdeg_zero (k : Type u) [Field k] :
    Algebra.trdeg k (k[X] ⧸ Ideal.span {(X : k[X]) ^ 2}) = 0 := by
  apply le_antisymm _ zero_le
  exact (Ideal.span {(X : k[X]) ^ 2}).trdeg_quotient_le_of_ne_bot
    (by simpa only [ne_eq, Ideal.span_singleton_eq_bot] using
      pow_ne_zero 2 (X_ne_zero (R := k))) (by simp)

/-- A nonzero nilpotent remains in exactly the quotient used above. -/
theorem double_point_has_nonzero_nilpotent (k : Type u) [Field k] :
    let I : Ideal k[X] := Ideal.span {(X : k[X]) ^ 2}
    Ideal.Quotient.mk I X ≠ 0 ∧ (Ideal.Quotient.mk I X) ^ 2 = 0 := by
  dsimp only
  constructor
  · intro h
    have hdiv : (X : k[X]) ^ 2 ∣ X :=
      Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h)
    have hc := (X_pow_dvd_iff.mp hdiv) 1 (by decide)
    simp at hc
  · rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_singleton _)

open Lean in
run_cmd do
  for name in #[``AlgebraicIndependent.transcendental_of_comp_of_regular_ker,
      ``AlgebraicIndependent.option_of_comp_of_regular_ker,
      ``Ideal.trdeg_quotient_le_of_regular_mem, ``Ideal.trdeg_quotient_le_of_ne_bot,
      ``actual_quotient_dimension_drop, ``regular_kernel_extends_family,
      ``double_point_trdeg_zero, ``double_point_has_nonzero_nilpotent] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Quotient transcendence-degree audit passed: standard foundations only."

end Motivic.MotivicTest.QuotientTrdeg
