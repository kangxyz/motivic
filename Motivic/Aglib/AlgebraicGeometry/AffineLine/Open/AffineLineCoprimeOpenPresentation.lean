/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.AffineLine.Open.AffineLineReducedComplement
public import Mathlib.RingTheory.Ideal.MonicSpan
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.Algebra.Squarefree.Basic

/-! # Coprime monic equations for the original nested affine-line opens

The equations generate the full reduced complement ideals of the original
opens. Thus all asserted basic-open equalities are literal, not replacement
models or merely abstract scheme isomorphisms. The field may be finite.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry TopologicalSpace Polynomial
universe u
namespace AlgebraicGeometry.Scheme.AffineLineReducedComplement
variable {k : Type u} [Field k]

/-- A nonempty original open has a monic squarefree defining polynomial, generating
its full reduced complement ideal. -/
theorem exists_monic_squarefree_presentation
    (U : (line k).Opens) (hU : (U : Set (line k)).Nonempty) :
    ∃ f : k[X], f.Monic ∧ Squarefree f ∧
      complementIdeal U = Ideal.span {f} ∧ PrimeSpectrum.basicOpen f = U := by
  have hη : genericPoint (line k) ∈ U :=
    ((genericPoint_spec (line k)).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  obtain ⟨a, ha, hD⟩ := exists_nonzero_basicOpen U hη
  have hI : complementIdeal U ≠ ⊥ := by
    intro h
    have hm := mem_complementIdeal U hD
    rw [h, Ideal.mem_bot] at hm
    exact ha hm
  obtain ⟨f, hf, hIf⟩ := Polynomial.exists_monic_span (complementIdeal U) hI
  have hrad : (Ideal.span ({f} : Set k[X])).IsRadical := by
    rw [← hIf]
    exact PrimeSpectrum.isRadical_vanishingIdeal _
  refine ⟨f, hf, (isRadical_iff_span_singleton.mpr hrad).squarefree hf.ne_zero, hIf, ?_⟩
  apply TopologicalSpace.Opens.ext
  rw [PrimeSpectrum.basicOpen_eq_zeroLocus_compl, ← PrimeSpectrum.zeroLocus_span, ← hIf,
    complementIdeal, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
  change (closure ((U : Set (line k))ᶜ))ᶜ = (U : Set (line k))
  rw [U.isOpen.isClosed_compl.closure_eq, compl_compl]

/-- Nested nonempty affine-line opens admit coprime monic equations retaining
both original opens exactly. There is no evaluation-unit condition on `g`. -/
theorem exists_coprime_monic_open_presentation
    (U V : (line k).Opens) (hVU : V ≤ U) (hV : (V : Set (line k)).Nonempty) :
    ∃ f g : k[X], f.Monic ∧ g.Monic ∧ IsCoprime f g ∧
      PrimeSpectrum.basicOpen f = U ∧ PrimeSpectrum.basicOpen (f * g) = V := by
  obtain ⟨f, hf, _, hIf, hUf⟩ := exists_monic_squarefree_presentation U (hV.mono hVU)
  obtain ⟨h, hh, hsq, hIh, hVh⟩ := exists_monic_squarefree_presentation V hV
  have hle : complementIdeal V ≤ complementIdeal U :=
    PrimeSpectrum.vanishingIdeal_anti_mono (Set.compl_subset_compl.mpr hVU)
  have hfh : f ∣ h := by
    apply Ideal.mem_span_singleton.mp
    rw [← hIf]
    apply hle
    rw [hIh]
    exact Ideal.subset_span (Set.mem_singleton h)
  obtain ⟨g, hg⟩ := hfh
  have hmg : g.Monic := hf.of_mul_monic_left (hg ▸ hh)
  have hcop : IsCoprime f g := (IsRelPrime.of_squarefree_mul (hg ▸ hsq)).isCoprime
  exact ⟨f, g, hf, hmg, hcop, hUf, hg ▸ hVh⟩

end AlgebraicGeometry.Scheme.AffineLineReducedComplement
