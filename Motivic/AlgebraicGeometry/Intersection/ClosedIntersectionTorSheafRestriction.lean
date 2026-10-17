/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Intersection.ClosedIntersectionTorRestriction
public import Motivic.AlgebraicGeometry.Modules.AffineOpenTildeRestriction

/-!
# Actual restriction of closed-intersection Tor chart sheaves

The real chart coefficient restriction and the canonical affine-open tilde
comparison construct a sheaf restriction isomorphism on the actual closed
inverse-image opens. No transition isomorphism or geometric cocycle is assumed.
The identity and composition equations, and effective finite-cover assembly,
remain subsequent proofs.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.Intersection

variable {P T D W : Scheme.{u}} (i : T ⟶ P) (j : D ⟶ P)
  (a : W ⟶ D) (b : W ⟶ T) [IsClosedImmersion i] [IsClosedImmersion j]
  (sq : IsPullback a b j i)

/-- Refinement of the genuine Tor chart sheaf along the actual closed-open inclusion. -/
def closedIntersectionTorSheafRestrictionIso {U V : P.affineOpens} (h : U ≤ V) (n : ℕ) :
    (Scheme.Modules.restrictFunctor (W.homOfLE ((a ≫ j).preimage_mono h))).obj
        (closedIntersectionTorChartSheaf i a b j sq V n) ≅
      closedIntersectionTorChartSheaf i a b j sq U n :=
  (AffineOpenTilde.restrictionIso
      (U := closedIntersectionAffineOpen i a b j sq U)
      (V := closedIntersectionAffineOpen i a b j sq V)
      ((a ≫ j).preimage_mono h)).app (closedIntersectionAffineTor i a b j sq V n) ≪≫
    (AffineOpenTilde.chartTilde (closedIntersectionAffineOpen i a b j sq U)).mapIso
      (closedIntersectionAffineTorRestrictionIso i j a b sq h n)

/-- The sheaf transition is precisely the actual geometric comparison followed by
sheafification of the canonical original coordinate-module restriction. -/
theorem closedIntersectionTorSheafRestrictionIso_hom {U V : P.affineOpens}
    (h : U ≤ V) (n : ℕ) :
    (closedIntersectionTorSheafRestrictionIso i j a b sq h n).hom =
      (AffineOpenTilde.restrictionIso
        (U := closedIntersectionAffineOpen i a b j sq U)
        (V := closedIntersectionAffineOpen i a b j sq V)
        ((a ≫ j).preimage_mono h)).hom.app (closedIntersectionAffineTor i a b j sq V n) ≫
      (AffineOpenTilde.chartTilde (closedIntersectionAffineOpen i a b j sq U)).map
        (closedIntersectionAffineTorRestrictionIso i j a b sq h n).hom := rfl

end Motivic.Intersection
