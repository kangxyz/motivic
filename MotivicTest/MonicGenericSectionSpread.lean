/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Sections.MonicGenericSectionSpread
public import Lean
/-! # Direct consumers preserve the original generic section of the nonreduced divisor -/
public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open Scheme.GenericSection
universe u
namespace MotivicTest.MonicGenericSectionSpread

theorem whole_monic_divisor (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (p : R[X]) (hp : p.Monic) {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of (AdjoinRoot p))) [Etale f]
    (s : genericFiber R (AdjoinRoot p) ⟶ Y)
    (hs : s ≫ f = pullback.fst (baseMap R (AdjoinRoot p)) (genericMap R)) :
    ∃ (r : R) (hr : r ≠ 0) (t : awayFiber R (AdjoinRoot p) r ⟶ Y),
      t ≫ f = pullback.fst (baseMap R (AdjoinRoot p)) (awayMap R r) ∧
      genericFiberToAway R (AdjoinRoot p) r hr ≫ t = s :=
  exists_monic_section_over_away R p hp f s hs

/-- Explicit square-zero monic divisor: no domain/reducedness premise can be hidden
on the divisor, and no rationality assumption on its components is supplied. -/
theorem square_zero_divisor (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of (AdjoinRoot ((X : R[X]) ^ 2)))) [Etale f]
    (s : genericFiber R (AdjoinRoot ((X : R[X]) ^ 2)) ⟶ Y)
    (hs : s ≫ f = pullback.fst (baseMap R _) (genericMap R)) :
    ∃ (r : R) (hr : r ≠ 0) (t : awayFiber R (AdjoinRoot ((X : R[X]) ^ 2)) r ⟶ Y),
      t ≫ f = pullback.fst (baseMap R _) (awayMap R r) ∧
      genericFiberToAway R _ r hr ≫ t = s :=
  exists_monic_section_over_away R (X ^ 2) (monic_X.pow 2) f s hs

open Lean in
run_cmd do
  for name in #[``whole_monic_divisor, ``square_zero_divisor,
      ``exists_monic_section_over_away, ``exists_section_over_away,
      ``exists_generic_open_section, ``Scheme.exists_generic_open_section_of_stalk_sections,
      ``stalkToGenericFiber, ``Scheme.hom_ext_of_fromSpecStalk] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original monic generic section and actual localization equality: audited."

end MotivicTest.MonicGenericSectionSpread
