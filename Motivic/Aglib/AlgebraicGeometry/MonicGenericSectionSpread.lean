/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.FiniteGenericSectionPrincipalSpread
public import Motivic.Aglib.AlgebraicGeometry.PolynomialOpenQuotient

/-! # Spreading sections over the whole original monic divisor -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Polynomial
universe u
namespace AlgebraicGeometry.Scheme.GenericSection

/-- A section over the entire generic monic divisor extends over a nonzero
base localization, retaining the original section exactly. The divisor may
be disconnected, inseparable, nonreduced, or empty. -/
theorem exists_monic_section_over_away
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (p : R[X]) (hp : p.Monic) {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of (AdjoinRoot p))) [LocallyOfFiniteType f]
    (s : genericFiber R (AdjoinRoot p) ⟶ Y)
    (hs : s ≫ f = pullback.fst (baseMap R (AdjoinRoot p)) (genericMap R)) :
    ∃ (r : R) (hr : r ≠ 0) (t : awayFiber R (AdjoinRoot p) r ⟶ Y),
      t ≫ f = pullback.fst (baseMap R (AdjoinRoot p)) (awayMap R r) ∧
      genericFiberToAway R (AdjoinRoot p) r hr ≫ t = s := by
  have : IsFinite (baseMap R (AdjoinRoot p)) := PolynomialOpenQuotient.source_finite p hp
  have : Flat (baseMap R (AdjoinRoot p)) := PolynomialOpenQuotient.source_flat p hp
  exact exists_section_over_away R (AdjoinRoot p) f s hs

end AlgebraicGeometry.Scheme.GenericSection
