/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Smooth.Locality
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.FiniteFlat
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Proper flat Cartier subschemes of smooth relative curves

A closed immersion with locally rank-one actual ideal in a smooth relative
curve is finite over the base if its composite is flat and proper. Flatness
is essential to the relative Cartier locality theorem: an arbitrary absolute
Cartier divisor can contain whole fibers. The actual direct image of the
structure module is finite locally free. The base may be nonreduced and
non-Noetherian; no field, perfection, or infinitude assumption is used.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

open Scheme.Modules Scheme.Modules.Invertible

variable {S C D : Scheme.{u}} (p : C ⟶ S) (i : D ⟶ C)
  [SmoothOfRelativeDimension 1 p] [IsClosedImmersion i]
  (hI : IsLocallyRankOne C (idealModule i)) [Flat (i ≫ p)] [IsProper (i ≫ p)]

include hI in
/-- Properness upgrades the genuine relative Cartier quasi-finiteness supplier
to finiteness; the actual composite is also locally finitely presented. -/
theorem isFinite_and_locallyOfFinitePresentation_of_proper_flat_cartier :
    IsFinite (i ≫ p) ∧ LocallyOfFinitePresentation (i ≫ p) := by
  obtain ⟨hquasi, hfp⟩ :=
    locallyQuasiFinite_and_locallyOfFinitePresentation_of_smooth_cartier
      S C D p i inferInstance inferInstance hI inferInstance
  have := hquasi
  exact ⟨IsFinite.of_isProper_of_locallyQuasiFinite (i ≫ p), hfp⟩

include hI in
/-- A proper flat Cartier subscheme of a smooth relative curve has actual
finite local bases for the direct image of its original structure sheaf. -/
theorem pushforwardStructureSheaf_isFiniteLocallyFree_of_proper_flat_cartier :
    IsFiniteLocallyFree S (pushforwardStructureSheaf (i ≫ p)) := by
  obtain ⟨hfin, hfp⟩ :=
    isFinite_and_locallyOfFinitePresentation_of_proper_flat_cartier p i hI
  have := hfin
  have := hfp
  exact finiteFlat_pushforwardStructureSheaf_isFiniteLocallyFree (i ≫ p)

end AlgebraicGeometry.Scheme.Hom
