/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.CompositionSupport
public import Motivic.AlgebraicGeometry.SmoothSiteNoetherian

/-!
# Noetherian incidence supports

The actual incidence scheme of two finite-correspondence generators is finite
over the original source, hence Noetherian whenever that source is Noetherian.
This derives the finite-component and local Noetherian-ring hypotheses needed
for fundamental and intersection-cycle constructions. The incidence scheme is
not assumed reduced or integral, and no multiplicity is assigned here.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondenceGenerator

variable {S X Y Z : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S}
  (A : FiniteCorrespondenceGenerator f g) (B : FiniteCorrespondenceGenerator g h)

instance isNoetherian_incidence [IsNoetherian X] : IsNoetherian (A.incidence B) :=
  isNoetherian_of_finiteType (A.incidenceSource B)

/-- There are finitely many actual incidence components, before assigning Tor multiplicities. -/
theorem finite_incidence_components [IsNoetherian X] :
    (irreducibleComponents (A.incidence B)).Finite :=
  finite_irreducibleComponents_of_isNoetherian

/-- Every local ring of incidence is Noetherian. -/
theorem incidence_stalk_isNoetherian [IsNoetherian X] (w : A.incidence B) :
    IsNoetherianRing ((A.incidence B).presheaf.stalk w) := inferInstance

end Motivic.FiniteCorrespondenceGenerator
