/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Support.Noetherian

/-!
# Noetherian incidence over the actual smooth site

The finite-component and local-ring hypotheses are obtained from smooth-site
objects and genuine finite-correspondence projections, without assuming the
incidence scheme integral or reduced.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Motivic

universe u

namespace MotivicTest.CorrespondenceNoetherianSupport
open _root_.AlgebraicGeometry.Scheme (SmoothSite)

variable (K : Type u) [Field K] (X Y Z : SmoothSite (Spec (.of K)))
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)

/-- Actual incidence over a smooth field-valued object is Noetherian. -/
theorem incidence_noetherian : IsNoetherian (A.incidence B) :=
  FiniteCorrespondenceGenerator.isNoetherian_incidence (X := X.left) A B

/-- Its irreducible-component set is finite without a connectedness assumption. -/
theorem incidence_components_finite : (irreducibleComponents (A.incidence B)).Finite :=
  FiniteCorrespondenceGenerator.finite_incidence_components (X := X.left) A B

/-- Its stalks are actual Noetherian rings, suitable for local intersection algebra. -/
theorem incidence_local_ring_noetherian (w : A.incidence B) :
    IsNoetherianRing ((A.incidence B).presheaf.stalk w) :=
  FiniteCorrespondenceGenerator.incidence_stalk_isNoetherian (X := X.left) A B w

end MotivicTest.CorrespondenceNoetherianSupport
