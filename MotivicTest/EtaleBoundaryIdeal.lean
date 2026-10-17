/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.EtaleBoundaryIdeal

/-! Original diagonal boundary trivialization, retaining arbitrary boundary rings. -/

@[expose] public section
noncomputable section
set_option linter.hashCommand false

#print axioms AlgebraicGeometry.Scheme.Hom.neighborhoodBoundaryIdealIso
#print axioms AlgebraicGeometry.Scheme.Hom.compactificationBoundaryIdealIso
#print axioms AlgebraicGeometry.Scheme.Hom.compactificationBoundaryDivisorIso
#print axioms AlgebraicGeometry.Scheme.Hom.compactificationBoundaryDivisorIso_of_smooth_near_graph

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

example (R B : Type u) [CommRing R] [CommRing B] (z : Polynomial R →+* B)
    {C Y : Scheme.{u}} (q : C ⟶ Spec (.of R)) [IsSeparated q]
    (j : Y ⟶ C) [IsOpenImmersion j]
    (p : Y ⟶ Spec (.of (Polynomial R))) [Flat p]
    (hq : j ≫ q = p ≫ Scheme.Hom.boundaryLineProjection R)
    (s : Spec (.of B) ⟶ Y) (h : s ≫ p = Scheme.Hom.boundaryCoordinateMap R B z)
    (H : IsPullback s (𝟙 _) p (Scheme.Hom.boundaryCoordinateMap R B z)) :
    SheafOfModules.unit (pullback (j ≫ q) (s ≫ j ≫ q)).ringCatSheaf ≅
      (Scheme.Modules.pullback (Scheme.Hom.graphBoundaryRestriction q j s)).obj
        (Scheme.Hom.idealModule (Scheme.Hom.compactificationGraph q j)) :=
  Scheme.Hom.compactificationBoundaryIdealIso R B z q j p hq s h H
