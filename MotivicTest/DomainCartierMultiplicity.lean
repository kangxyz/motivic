/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Multiplicity.Cartier.Domain
public import Lean.Util.CollectAxioms

/-!
# Actual local-domain Cartier multiplicities

The Euler statement permits torsion in the finite module. The quotient-length
consumer separately supplies genuine regularity; Artinian support proves the
length finite before conversion to an integer.
-/

@[expose] public noncomputable section

open _root_.ChainComplex.Koszul _root_.HomologicalComplex.ModuleLengthEuler

universe u

namespace MotivicTest.DomainCartierMultiplicity

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
  (M : ModuleCat.{u} R) [Module.Finite R M] (t : R)
  [IsArtinianRing (R ⧸ Ideal.ofList [t])]

/-- Generic length controls the genuine Euler characteristic, even for a torsion module. -/
theorem actual_euler (ht : IsSMulRegular R t) (hm : t ∈ IsLocalRing.maximalIdeal R) :
    chainEuler (coefficientComplex M [t]) (domainCartierFiniteHomology (R := R) M t) =
      domainGenericLength M * ((Module.length R (R ⧸ Ideal.ofList [t])).toNat : ℤ) :=
  domainCartier_chainEuler M t ht hm

/-- The actual quotient formula uses the additionally proved module regularity. -/
theorem actual_quotient (ht : IsSMulRegular R t) (hm : t ∈ IsLocalRing.maximalIdeal R)
    (hM : IsSMulRegular M t) :
    ((Module.length R (SingleQuotient M t)).toNat : ℤ) =
      domainGenericLength M * ((Module.length R (R ⧸ Ideal.ofList [t])).toNat : ℤ) :=
  domainCartier_quotient_length M t ht hm hM

omit [IsDomain R] [IsLocalRing R] in
/-- The quotient length is finite independently of any integer equality. -/
theorem actual_finiteness (hM : IsSMulRegular M t) :
    Module.length R (SingleQuotient M t) ≠ ⊤ :=
  domainCartier_quotient_length_ne_top M t hM

open Lean in
run_cmd do
  for name in #[``_root_.ChainComplex.Koszul.domainGenericPrime,
      ``_root_.ChainComplex.Koszul.domainGenericLength,
      ``_root_.ChainComplex.Koszul.domainCartierFiniteHomology,
          ``_root_.ChainComplex.Koszul.domainCartier_chainEuler,
      ``_root_.ChainComplex.Koszul.domainCartier_quotient_length,
          ``_root_.ChainComplex.Koszul.domainCartier_quotient_length_ne_top,
      ``actual_euler, ``actual_quotient, ``actual_finiteness] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual Cartier multiplicities use only standard Lean foundations."

end MotivicTest.DomainCartierMultiplicity
