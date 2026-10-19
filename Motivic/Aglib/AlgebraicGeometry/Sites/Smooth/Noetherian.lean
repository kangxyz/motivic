/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Basic
public import Motivic.Aglib.AlgebraicGeometry.Scheme.FiniteTypeNoetherian

/-!
# Noetherian smooth sites
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

namespace SmoothSite

variable {S : Scheme.{u}}

instance isNoetherian_left [IsNoetherian S] (X : SmoothSite S) : IsNoetherian X.left :=
  isNoetherian_of_finiteType (Y := S) X.hom

/-- Smooth-site objects over a field have finitely many irreducible components. -/
theorem finite_irreducibleComponents (K : Type u) [Field K] (X : SmoothSite (Spec (.of K))) :
    (irreducibleComponents X.left).Finite :=
  finite_irreducibleComponents_of_isNoetherian

end SmoothSite

end AlgebraicGeometry.Scheme
