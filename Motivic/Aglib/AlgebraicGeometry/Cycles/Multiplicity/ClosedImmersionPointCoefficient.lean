/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.ClosedImmersionGenericCycleCoefficient

/-!
# Closed fundamental-cycle coefficients at specified points

A closed immersion has residue degree one. At an original ambient point its
full fundamental-cycle coefficient is the actual quotient length if every
preimage is generic, and is zero if no preimage is generic. The ambient point
need not itself be generic, and empty inverse images are handled explicitly.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme

variable {E P : Scheme.{u}} (j : E ⟶ P) [IsClosedImmersion j] [IsNoetherian E]

/-- A specified-point version of the closed-support quotient-length formula. -/
theorem closedImmersion_fundamentalCoefficient_eq_length_at
    (x : P) (hx : ∀ y : E, j y = x → y ∈ genericPoints E) :
    IntegralCycle.toPoints (IntegralCycle.finitePushforward j (fundamentalCycle E)) x =
      ((Module.length (P.presheaf.stalk x)
        ((P.presheaf.stalk x) ⧸ j.ker.stalk x)).toNat : ℤ) := by
  classical
  rw [IntegralCycle.toPoints_finitePushforward_apply, toPoints_fundamentalCycle,
    residuePushforward_eq_mapDomain_of_surjectiveOnStalks]
  change Finsupp.mapDomain j (fundamentalPointCycle E) x = _
  by_cases h : x ∈ Set.range j
  · obtain ⟨y, rfl⟩ := h
    rw [Finsupp.mapDomain_apply_of_injective j.isEmbedding.injective,
      fundamentalPointCycle_apply, dite_eq_left (hx y rfl), j.ker_stalk]
    have hlength : Module.length (P.presheaf.stalk (j y))
        ((P.presheaf.stalk (j y)) ⧸ RingHom.ker (j.stalkMap y).hom) =
        Module.length (E.presheaf.stalk y) (E.presheaf.stalk y) :=
      (Module.length_eq_of_surjective
        (Ideal.Quotient.mk_surjective (I := RingHom.ker (j.stalkMap y).hom))).trans
          (ringLength_eq_of_ringEquiv (stalkQuotientKerEquiv j y))
    rw [hlength]
    rfl
  · rw [Finsupp.mapDomain_of_notMem_range _ _ h]
    have : Subsingleton ((P.presheaf.stalk x) ⧸ j.ker.stalk x) :=
      Ideal.Quotient.subsingleton_iff.mpr
          (_root_.AlgebraicGeometry.Scheme.Hom.closedImmersion_ker_stalk_eq_top j h)
    simp only [Module.length_eq_zero, ENat.toNat_zero, Nat.cast_zero]

/-- At a point with no generic preimage the full pushed coefficient vanishes. -/
theorem closedImmersion_fundamentalCoefficient_eq_zero_at
    (x : P) (hx : ∀ y : E, j y = x → y ∉ genericPoints E) :
    IntegralCycle.toPoints (IntegralCycle.finitePushforward j (fundamentalCycle E)) x = 0 := by
  classical
  rw [IntegralCycle.toPoints_finitePushforward_apply, toPoints_fundamentalCycle,
    residuePushforward_eq_mapDomain_of_surjectiveOnStalks]
  change Finsupp.mapDomain j (fundamentalPointCycle E) x = _
  by_cases h : x ∈ Set.range j
  · obtain ⟨y, rfl⟩ := h
    rw [Finsupp.mapDomain_apply_of_injective j.isEmbedding.injective,
      fundamentalPointCycle_apply, dite_eq_right (hx y rfl)]
  · exact Finsupp.mapDomain_of_notMem_range _ _ h

end AlgebraicGeometry
