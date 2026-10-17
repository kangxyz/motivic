/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.SmoothSiteReduced
public import Motivic.AlgebraicGeometry.SmoothSiteNoetherian
public import Motivic.AlgebraicGeometry.SmoothSiteBaseChange
public import Motivic.AlgebraicGeometry.Correspondences.ComponentGraphs

/-!
# Reduced smooth objects and their actual component graph cycles

Every field below is arbitrary. Every smooth source below is an actual
smooth-site object, with no reducedness, nonemptiness, connectedness, or
integrality assumption. Reducedness and Noetherianity are derived from the
structure map before constructing the existing componentwise graph cycle.
The final consumer allows an arbitrary ground-field extension.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Motivic

universe u

namespace MotivicTest.SmoothSiteReduced

variable (K L : Type u) [Field K] [Field L]

/-- Smoothness over any field supplies actual scheme reducedness. -/
theorem smooth_source_reduced {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [Smooth f] :
    IsReduced X :=
  isReduced_of_smooth_over_field K f

/-- Every smooth-site object over a field is reduced without extra hypotheses. -/
theorem object_reduced (X : SmoothSite (Spec (.of K))) : IsReduced X.left := inferInstance

/-- Its actual local rings are reduced. -/
theorem stalk_reduced (X : SmoothSite (Spec (.of K))) (x : X.left) :
    _root_.IsReduced (X.left.presheaf.stalk x) := inferInstance

/-- The existing graph construction gives a cycle for every smooth-site morphism. -/
noncomputable def graph {X Y : SmoothSite (Spec (.of K))} (φ : X ⟶ Y) :
    FiniteCorrespondence X.hom Y.hom := by
  simpa only [MorphismProperty.Over.w] using componentGraphCycle φ.left Y.hom

/-- The graph has literal source-component support and a finite projection. -/
theorem component_finite_with_literal_image {X Y : SmoothSite (Spec (.of K))}
    (φ : X ⟶ Y) (Z : Set X.left) (hZ : Z ∈ irreducibleComponents X.left) :
    IsFinite (componentGraphGenerator φ.left Y.hom Z hZ).projection ∧
      Set.range (componentGraphGenerator φ.left Y.hom Z hZ).projection = Z :=
  ⟨inferInstance, componentGraphGenerator_range φ.left Y.hom Z hZ⟩

/-- Every source component occurs in the graph cycle with multiplicity one. -/
theorem component_multiplicity {X Y : SmoothSite (Spec (.of K))}
    (φ : X ⟶ Y) (Z : Set X.left) (hZ : Z ∈ irreducibleComponents X.left) :
    componentGraphCycle φ.left Y.hom (componentGraphGenerator φ.left Y.hom Z hZ) = 1 :=
  componentGraphCycle_coefficient φ.left Y.hom Z hZ

/-- Every smooth-site object has its actual componentwise diagonal cycle. -/
noncomputable def diagonal (X : SmoothSite (Spec (.of K))) :
    FiniteCorrespondence X.hom X.hom := graph K (𝟙 X)

/-- An arbitrary change of ground field preserves the proved reducedness. -/
theorem field_baseChange_reduced (f : K →+* L) (X : SmoothSite (Spec (.of K))) :
    IsReduced (((SmoothSite.baseChange (Spec.map (CommRingCat.ofHom f))).obj X).left) :=
  inferInstance

end MotivicTest.SmoothSiteReduced
