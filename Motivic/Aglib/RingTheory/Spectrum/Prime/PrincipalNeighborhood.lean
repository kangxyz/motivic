/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Principal neighborhoods of prime ideals
-/

@[expose] public noncomputable section

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open TopologicalSpace
universe u
namespace PrimeSpectrum

/-- A closed subset inside an open admits a principal neighborhood congruent to one
modulo its original ideal. The ideal need not be radical. -/
theorem exists_basicOpen_between_zeroLocus (R : Type u) [CommRing R]
    (J : Ideal R) (U : Opens (PrimeSpectrum R))
    (hU : zeroLocus (J : Set R) ⊆ U) :
    ∃ r : R, r - 1 ∈ J ∧ basicOpen r ≤ U := by
  obtain ⟨I, hI⟩ := (isClosed_iff_zeroLocus_ideal (U : Set (PrimeSpectrum R))ᶜ).mp
    U.isOpen.isClosed_compl
  have htop : I ⊔ J = ⊤ := by
    by_contra h
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (I ⊔ J) h
    let x : PrimeSpectrum R := ⟨M, hM.isPrime⟩
    have hxI : x ∈ zeroLocus (I : Set R) := fun _ ha => hle ((show I ≤ I ⊔ J from le_sup_left) ha)
    have hxJ : x ∈ zeroLocus (J : Set R) := fun _ ha => hle ((show J ≤ I ⊔ J from le_sup_right) ha)
    have hxnot : x ∈ (U : Set (PrimeSpectrum R))ᶜ := by rwa [hI]
    exact hxnot (hU hxJ)
  obtain ⟨r, hr, s, hs, hrs⟩ := Submodule.mem_sup.mp
    ((Ideal.eq_top_iff_one _).mp htop)
  refine ⟨r, ?_, ?_⟩
  · have : r - 1 = -s := by rw [← hrs]; abel
    rw [this]
    exact J.neg_mem hs
  · intro x hx
    by_contra hxU
    have hxI : x ∈ zeroLocus (I : Set R) := hI ▸ hxU
    exact hx (hxI hr)

end PrimeSpectrum
