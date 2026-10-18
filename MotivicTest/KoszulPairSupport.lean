/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.RingTheory.LocalLength.KoszulPairLocalSupport

/-!
# Consumers of support-sensitive Koszul finite length

These checks use the actual homology modules, including a cyclic coefficient
module with both equations zero. Only its supporting quotient is Artinian;
the ambient ring is not assumed Artinian and the equations are not regular.
The final consumer discharges finiteness from a local minimal-support prime.
-/

@[expose] public section

universe u v

open Module.KoszulPair

namespace MotivicTest.KoszulPairSupport

variable {R : Type u} [CommRing R]

example (M : Type v) [AddCommGroup M] [Module R M] (a b r : R)
    (hr : r ∈ Module.annihilator R M) (z : H₁ M a b) : r • z = 0 :=
  Module.mem_annihilator.mp (annihilator_le_annihilator_H₁ M a b hr) z

example (M : Type v) [AddCommGroup M] [Module R M] (a b : R) :
    Ideal.span ({a, b} : Set R) ⊔ Module.annihilator R M ≤
      Module.annihilator R (H₂ M a b) :=
  span_sup_annihilator_le_annihilator_H₂ M a b

example [IsNoetherianRing R] (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] (a b : R)
    [IsArtinianRing (R ⧸ (Ideal.span ({a, b} : Set R) ⊔ Module.annihilator R M))] :
    Module.length R (H₀ M a b) ≠ ⊤ ∧
      Module.length R (H₁ M a b) ≠ ⊤ ∧ Module.length R (H₂ M a b) ≠ ⊤ :=
  hasFiniteHomology_of_artinian_support_quotient M a b

/-- Zero equations still have finite homology on an Artinian cyclic support. -/
theorem finiteHomology_zero_pair_on_quotient [IsNoetherianRing R] (I : Ideal R)
    [IsArtinianRing (R ⧸ I)] : HasFiniteHomology (R ⧸ I) (0 : R) 0 := by
  have : IsArtinianRing (R ⧸ (Ideal.span ({(0 : R), 0} : Set R) ⊔ I)) := by
    rw [Ideal.span_insert_zero, Ideal.span_singleton_zero, bot_sup_eq]
    infer_instance
  apply hasFiniteHomology_of_artinian_quotient_of_le_annihilator (R ⧸ I) 0 0 I
  rw [Ideal.annihilator_quotient]

/-- Higher homology in the preceding example need not vanish. -/
theorem nontrivial_H₂_zero_pair_on_quotient (I : Ideal R) [I.IsMaximal] :
    Nontrivial (H₂ (R ⧸ I) (0 : R) 0) := by
  refine ⟨⟨⟨1, by simp⟩, 0, ?_⟩⟩
  intro h
  exact one_ne_zero (congrArg Subtype.val h)

/-- At a minimal prime over the equations and cyclic support, every actual
Koszul homology degree has finite length. -/
theorem finiteHomology_on_local_cyclic_support
    [IsNoetherianRing R] [IsLocalRing R] (I : Ideal R) (a b : R)
    (hm : IsLocalRing.maximalIdeal R ∈ (Ideal.span ({a, b} : Set R) ⊔ I).minimalPrimes) :
    HasFiniteHomology (R ⧸ I) a b := by
  apply hasFiniteHomology_of_mem_minimalPrimes_of_le_annihilator (R ⧸ I) a b I _ hm
  rw [Ideal.annihilator_quotient]

end MotivicTest.KoszulPairSupport
