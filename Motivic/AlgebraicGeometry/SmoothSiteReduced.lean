/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.SmoothSite
public import Motivic.AlgebraicGeometry.Scheme.SmoothReduced

/-!
# Reducedness of smooth-site objects over integral bases

This instance supplies actual reducedness from the smooth structure morphism
when the base is integral. In particular it applies over every field, including
imperfect fields. A smooth-site object can still be empty or disconnected.
Reducedness is deliberately not asserted over an arbitrary, possibly
nonreduced base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic.SmoothSite

/-- A smooth-site object over an integral base is reduced. -/
instance isReduced_left {S : Scheme.{u}} [IsIntegral S] (X : SmoothSite S) :
    IsReduced X.left :=
  isReduced_of_smooth_of_isIntegral (Y := S) X.hom

end Motivic.SmoothSite
