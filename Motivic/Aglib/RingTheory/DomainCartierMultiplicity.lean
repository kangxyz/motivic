/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.CartierCutLength
public import Motivic.Algebra.Homology.KoszulCycleReplacement

/-!
# Actual generic multiplicity of a Cartier cut over a local domain

Fixed-support replacement at the zero ideal reduces to its unique generic
prime. Its coefficient is the existing finite localized module length, not
an assumed rank. A regular Cartier scalar identifies the remaining ring
Euler characteristic with the literal cut length. Regularity on the module
is imposed only when replacing its Euler characteristic by a quotient length.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Motivic.LengthEuler

universe u

namespace Motivic.Koszul

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]

/-- The actual unique minimal prime of a domain, viewed in the fixed zero support. -/
abbrev domainGenericPrime : (⊥ : Ideal R).minimalPrimes :=
  ⟨⊥, by rw [Ideal.minimalPrimes_eq_subsingleton_self]; simp⟩

/-- The zero-support generic multiplicity retains its proved finite localized length. -/
def domainGenericLength (M : ModuleCat.{u} R) [Module.Finite R M] : ℤ :=
  fixedSupportGenericLength M ⊥ bot_le (domainGenericPrime (R := R))

variable (M : ModuleCat.{u} R) [Module.Finite R M] (t : R)
  [IsArtinianRing (R ⧸ Ideal.ofList [t])]

omit [IsDomain R] [IsLocalRing R] in
/-- The actual Artinian Cartier quotient supplies finite singleton homology. -/
theorem domainCartierFiniteHomology : FiniteHomology (coefficientComplex M [t]) := by
  let : IsArtinianRing (R ⧸ (Ideal.ofList [t] ⊔ (⊥ : Ideal R))) := by
    rw [sup_bot_eq]
    infer_instance
  exact finiteHomology_of_artinian_quotient_of_le_annihilator M [t] ⊥ bot_le

/-- Finite-module Cartier Euler length is the original generic length times
its ambient Cartier quotient length. The module need not be torsion-free. -/
theorem domainCartier_chainEuler
    (ht : IsSMulRegular R t) (hm : t ∈ IsLocalRing.maximalIdeal R) :
    chainEuler (coefficientComplex M [t]) (domainCartierFiniteHomology (R := R) M t) =
      domainGenericLength M * ((Module.length R (R ⧸ Ideal.ofList [t])).toNat : ℤ) := by
  let : IsArtinianRing (R ⧸ (Ideal.ofList [t] ⊔ (⊥ : Ideal R))) := by
    rw [sup_bot_eq]
    infer_instance
  have hs : ∀ a ∈ [t], a ∈ IsLocalRing.maximalIdeal R := by simpa using hm
  rw [fixedSupport_chainEuler_replacement M [t] ⊥ hs bot_le]
  rw [finsum_eq_single _ (domainGenericPrime (R := R)) (fun p hp => ?_)]
  · dsimp only [domainGenericPrime]
    rw [coefficient_chainEuler_eq_of_linearEquiv
      (ModuleCat.of R (R ⧸ (⊥ : Ideal R))) (ModuleCat.of R R)
      (AlgEquiv.quotientBot R R).toLinearEquiv [t] _
      (domainCartierFiniteHomology (ModuleCat.of R R) t),
      singleton_chainEuler_eq_ring_quotient_length t ht]
    rfl
  · apply False.elim
    apply hp
    apply Subtype.ext
    change (p : Ideal R) = ⊥
    simpa only [Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff]
      using p.property

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- With the additionally proved module regularity, the actual quotient length
has the same generic multiplicity formula; all lengths are genuine finite ones. -/
theorem domainCartier_quotient_length
    (ht : IsSMulRegular R t) (hm : t ∈ IsLocalRing.maximalIdeal R)
    (hM : IsSMulRegular M t) :
    ((Module.length R (SingleQuotient M t)).toNat : ℤ) =
      domainGenericLength M * ((Module.length R (R ⧸ Ideal.ofList [t])).toNat : ℤ) := by
  exact (singleton_chainEuler_eq_length (R := R) M t hM
    (domainCartierFiniteHomology (R := R) M t)).symm.trans
      (domainCartier_chainEuler M t ht hm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [IsDomain R] [IsLocalRing R] in
/-- Finiteness of the module quotient is established before integer conversion. -/
theorem domainCartier_quotient_length_ne_top (hM : IsSMulRegular M t) :
    Module.length R (SingleQuotient M t) ≠ ⊤ :=
  singleton_quotient_length_ne_top (R := R) M t hM
    (domainCartierFiniteHomology (R := R) M t)

end Motivic.Koszul
