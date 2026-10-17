/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.SmoothSite
public import Motivic.AlgebraicGeometry.Scheme.FiniteTypeNoetherian
public import Motivic.AlgebraicGeometry.Correspondences.Generators

/-!
# Noetherianity of smooth-site objects and correspondence supports

Smooth separated finite-type objects over a Noetherian base are genuinely
Noetherian schemes. In particular this holds over every field. Integral finite
correspondence supports over a Noetherian source are Noetherian as well.
These instances connect the geometric object category to the finite-component
and local-length prerequisites for cycle constructions. They do not assert that
every smooth object is integral, connected, or reduced by definition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic

namespace SmoothSite

variable {S : Scheme.{u}}

instance isNoetherian_left [IsNoetherian S] (X : SmoothSite S) : IsNoetherian X.left :=
  isNoetherian_of_finiteType (Y := S) X.hom

/-- Smooth-site objects over a field have finitely many irreducible components. -/
theorem finite_irreducibleComponents (K : Type u) [Field K] (X : SmoothSite (Spec (.of K))) :
    (irreducibleComponents X.left).Finite :=
  finite_irreducibleComponents_of_isNoetherian

end SmoothSite

namespace FiniteCorrespondenceGenerator

variable {S X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}

instance isNoetherian_scheme [IsNoetherian X] (Z : FiniteCorrespondenceGenerator f g) :
    IsNoetherian Z.scheme :=
  isNoetherian_of_finiteType Z.projection

/-- The local rings of the actual correspondence support are Noetherian. -/
theorem stalk_isNoetherian [IsNoetherian X] (Z : FiniteCorrespondenceGenerator f g)
    (z : Z.scheme) : IsNoetherianRing (Z.scheme.presheaf.stalk z) := inferInstance

end FiniteCorrespondenceGenerator

end Motivic
