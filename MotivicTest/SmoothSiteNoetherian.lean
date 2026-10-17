/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.SmoothSiteNoetherian
public import Motivic.AlgebraicGeometry.SmoothSiteBaseChange

/-!
# Noetherian consumers for smooth schemes and finite correspondences

These consumers derive the local finiteness hypotheses used in geometric cycle
constructions from the actual smooth-site and finite-projection data. No object
is assumed irreducible or connected, and a change of ground field can be
arbitrary rather than finite over the original field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Motivic

universe u

namespace MotivicTest.SmoothSiteNoetherian

variable (K L : Type u) [Field K] [Field L]

/-- Every actual smooth finite-type object over a field is Noetherian. -/
theorem object_noetherian (X : SmoothSite (Spec (.of K))) : IsNoetherian X.left := inferInstance

/-- Each actual correspondence support over a smooth object is Noetherian. -/
theorem correspondence_noetherian (X Y : SmoothSite (Spec (.of K)))
    (Z : FiniteCorrespondenceGenerator X.hom Y.hom) : IsNoetherian Z.scheme := by
  have : IsNoetherian X.left := inferInstance
  exact FiniteCorrespondenceGenerator.isNoetherian_scheme (X := X.left) Z

/-- There are only finitely many irreducible source components. -/
theorem finite_source_components (X : SmoothSite (Spec (.of K))) :
    (irreducibleComponents X.left).Finite :=
  SmoothSite.finite_irreducibleComponents K X

/-- An arbitrary field map produces another Noetherian smooth-site object. -/
theorem field_baseChange_noetherian (f : K →+* L) (X : SmoothSite (Spec (.of K))) :
    IsNoetherian (((SmoothSite.baseChange (Spec.map (CommRingCat.ofHom f))).obj X).left) :=
  inferInstance

end MotivicTest.SmoothSiteNoetherian
