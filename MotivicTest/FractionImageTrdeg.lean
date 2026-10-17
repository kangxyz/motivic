module

public import Motivic.Aglib.RingTheory.AlgebraicIndependent.FractionImageTrdeg
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Lean.Util.CollectAxioms

/-! # Fraction-source image transcendence-degree regression tests -/

@[expose] public noncomputable section

universe u

namespace Motivic.MotivicTest.FractionImageTrdeg

/-- The coefficient field may be an actual intermediate field of the fraction
field, with no coefficient-field algebra structure on the original domain. -/
theorem intermediate_field_subalgebra_algebraic
    {k C E : Type u} [Field k] [CommRing C] [IsDomain C] [Field E]
    [Algebra C E] [IsFractionRing C E] [Algebra k E]
    (K : IntermediateField k E) (S : Subalgebra K E)
    (hS : Set.range (algebraMap C E) ⊆ S) :
    Algebra.IsAlgebraic S E :=
  S.isAlgebraic_of_fractionRing_image_subset hS

/-- The equality concerns native transcendence degrees, rather than a supplied
algebraicity or transcendence-degree premise. -/
theorem intermediate_field_subalgebra_trdeg
    {k C E : Type u} [Field k] [CommRing C] [IsDomain C] [Field E]
    [Algebra C E] [IsFractionRing C E] [Algebra k E]
    (K : IntermediateField k E) (S : Subalgebra K E)
    (hS : Set.range (algebraMap C E) ⊆ S) :
    Algebra.trdeg K S = Algebra.trdeg K E :=
  S.trdeg_eq_of_fractionRing_image_subset hS

/-- An actual specialized quotient map is enough, with no reducedness,
primality, injectivity, or algebraicity premise on its source quotient. -/
theorem specialized_quotient_map_bounds_fraction_trdeg
    {K C R E : Type u} [Field K] [CommRing C] [IsDomain C] [CommRing R] [Field E]
    [Algebra C E] [IsFractionRing C E] [Algebra K R] [Algebra K E]
    (I : Ideal R) (f : (R ⧸ I) →ₐ[K] E)
    (hf : ∀ c : C, algebraMap C E c ∈ f.range) :
    Algebra.trdeg K E ≤ Algebra.trdeg K (R ⧸ I) :=
  f.trdeg_le_of_fractionRing_image_mem hf

/-- This is the range handoff from a surjective original-coordinate quotient
and an actual specialized map. The original source need not be a K-algebra. -/
theorem bound_from_surjective_original_source
    {K A C D E : Type u} [Field K] [CommRing A] [CommRing C] [IsDomain C]
    [CommRing D] [Field E] [Algebra C E] [IsFractionRing C E]
    [Algebra K D] [Algebra K E]
    (q : A →+* C) (hq : Function.Surjective q) (f : D →ₐ[K] E)
    (hf : ∀ a : A, algebraMap C E (q a) ∈ f.range) :
    Algebra.trdeg K E ≤ Algebra.trdeg K D := by
  apply f.trdeg_le_of_fractionRing_image_mem (C := C)
  intro c
  obtain ⟨a, rfl⟩ := hq c
  exact hf a

open Polynomial

/-- The actual evaluation map from a nonreduced double-point quotient. -/
def doublePointMap (k : Type u) [Field k] :
    (k[X] ⧸ Ideal.span {(X : k[X]) ^ 2}) →ₐ[k] k :=
  Ideal.Quotient.liftₐ _ (aeval (0 : k)) (by
    intro p hp
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp hp
    simp)

/-- The map theorem really applies to the double-point quotient. -/
theorem double_point_fraction_bound (k : Type u) [Field k] :
    Algebra.trdeg k k ≤ Algebra.trdeg k (k[X] ⧸ Ideal.span {(X : k[X]) ^ 2}) := by
  apply (doublePointMap k).trdeg_le_of_fractionRing_image_mem (C := k)
  intro c
  exact ⟨algebraMap k _ c, (doublePointMap k).commutes c⟩

/-- A nonzero nilpotent witnesses that this source is not a domain. -/
theorem double_point_source_has_nilpotent (k : Type u) [Field k] :
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
  for name in #[``Subalgebra.isAlgebraic_of_fractionRing_image_subset,
      ``Subalgebra.trdeg_eq_of_fractionRing_image_subset,
      ``AlgHom.trdeg_le_of_fractionRing_image_subset,
      ``AlgHom.trdeg_le_of_fractionRing_image_mem,
      ``intermediate_field_subalgebra_algebraic, ``intermediate_field_subalgebra_trdeg,
      ``specialized_quotient_map_bounds_fraction_trdeg, ``bound_from_surjective_original_source,
      ``doublePointMap, ``double_point_fraction_bound, ``double_point_source_has_nilpotent] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Fraction-image transcendence-degree audit passed: standard foundations only."

end Motivic.MotivicTest.FractionImageTrdeg
