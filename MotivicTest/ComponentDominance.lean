/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.ComponentDominance

/-!
# Consumers of geometric finite-base-change dominance

These consumers include arbitrary test schemes, a nonreduced affine test
algebra, a disconnected affine test algebra, and arbitrary smooth-site objects
without global integrality hypotheses. The resulting image is a genuine
finite-correspondence generator on the existing ideal-sheaf basis.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Motivic

universe u

namespace MotivicTest.ComponentDominance

/-- The geometric endpoint accepts arbitrary locally finite-type test schemes. -/
theorem actual_pullback_generalizing
    {A B Y : Scheme.{u}} (g : A ⟶ Y) (f : B ⟶ Y)
    [IsFinite f] [Surjective f] [LocallyOfFiniteType g]
    [IsIntegral B] [IsIntegral Y]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) :
    GeneralizingMap (pullback.fst g f) :=
  generalizingMap_pullbackFst_normal_base g f hY

/-- The arbitrary finite-type test algebra has no reducedness or domain assumption. -/
theorem arbitrary_affine_test (k A : Type u) [Field k] [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] :
    GeneralizingMap (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A)))
      (Spec.map (CommRingCat.ofHom (algebraMap k k)))) := by
  apply generalizingMap_pullbackFst_spec k A k
  intro p
  exact ⟨p, by ext; simp⟩

/-- The actual dual-number affine scheme is permitted as the test scheme. -/
theorem nonreduced_affine_test (k : Type u) [Field k] :
    let A := Polynomial k ⧸ Ideal.span ({Polynomial.X ^ 2} : Set (Polynomial k))
    GeneralizingMap (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A)))
      (Spec.map (CommRingCat.ofHom (algebraMap k k)))) := by
  dsimp only
  exact arbitrary_affine_test k _

/-- A disconnected test scheme is also permitted, independently of the integral base. -/
theorem disconnected_affine_test (k : Type u) [Field k] :
    GeneralizingMap (pullback.fst
      (Spec.map (CommRingCat.ofHom (algebraMap k (k × k))))
      (Spec.map (CommRingCat.ofHom (algebraMap k k)))) :=
  arbitrary_affine_test k (k × k)

variable (k : Type u) [Field k]
  {X Y Z : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)

/-- The intermediate smooth object may have any number of components. -/
theorem arbitrary_smooth_incidence : GeneralizingMap (A.incidenceFst B) :=
  A.generalizingMap_incidenceFst_smooth k B

/-- Every component of the actual incidence surjects onto the first support. -/
theorem each_component_surjective (x : genericPoints (A.incidence B)) :
    Function.Surjective
      ((IntegralClosedSubscheme.pointClosure x.val).val.subschemeι ≫ A.incidenceFst B) :=
  A.incidence_component_surjective k B x

/-- The source image is the prescribed component, even for a disconnected source. -/
theorem exact_source_component (x : genericPoints (A.incidence B)) :
    Set.range ((IntegralClosedSubscheme.pointClosure x.val).val.subschemeι ≫
      A.incidenceSource B) = Set.range A.projection :=
  A.range_incidence_component_source k B x

/-- The actual finite-image ideal satisfies all generator axioms unconditionally. -/
theorem actual_image_admissible (x : genericPoints (A.incidence B)) :
    IsFiniteCorrespondenceGenerator X.hom Z.hom
      ((IntegralClosedSubscheme.pointClosure x.val).finiteImage (A.incidenceMap B)).val :=
  (A.smoothIncidenceComponentGenerator k B x).property

/-- Different genuine intermediate components give empty incidence. -/
theorem distinct_components_empty
    (C : Set Y.left) (hC : C ∈ irreducibleComponents Y.left)
    (hA : Set.range A.targetProjection ⊆ C) (hne : C ≠ Set.range B.projection) :
    IsEmpty (A.incidence B) :=
  A.incidence_isEmpty_of_distinct_component k B C hC hA hne

end MotivicTest.ComponentDominance
