/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Kaehler.JacobiZariski

/-!
# A differential criterion for étaleness

For a tower `R → S → T` with vanishing first cotangent homology of `T/R`,
an isomorphism on base-changed differentials implies that `T/S` is formally étale.
This applies in particular when `T` is smooth over `R`.
-/

@[expose] public section

namespace Algebra

variable (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- The Jacobi–Zariski criterion for formal étaleness over an intermediate ring. -/
theorem FormallyEtale.of_bijective_mapBaseChange
    [Subsingleton (H1Cotangent R T)]
    (h : Function.Bijective (KaehlerDifferential.mapBaseChange R S T)) :
    FormallyEtale S T := by
  constructor
  · apply subsingleton_of_forall_eq 0
    intro x
    obtain ⟨y, rfl⟩ := KaehlerDifferential.map_surjective R S T x
    exact (KaehlerDifferential.exact_mapBaseChange_map R S T y).mpr (h.surjective y)
  · apply subsingleton_of_forall_eq 0
    intro x
    have hx : H1Cotangent.δ R S T x = 0 := by
      apply h.injective
      rw [map_zero]
      exact (H1Cotangent.exact_δ_mapBaseChange R S T _).mpr ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := (H1Cotangent.exact_map_δ R S T x).mp hx
    rw [Subsingleton.elim y 0, map_zero]

/-- Finite presentation upgrades the differential criterion to étaleness. -/
theorem Etale.of_bijective_mapBaseChange
    [Subsingleton (H1Cotangent R T)] [FinitePresentation S T]
    (h : Function.Bijective (KaehlerDifferential.mapBaseChange R S T)) :
    Etale S T where
  formallyEtale := FormallyEtale.of_bijective_mapBaseChange R S T h

end Algebra
