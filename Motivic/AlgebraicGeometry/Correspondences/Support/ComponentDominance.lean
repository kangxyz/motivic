/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Generalizing.Components

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.BaseChange.Generalizing
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Admissibility
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Normal

/-!
# Component dominance of finite-correspondence incidence

The intermediate smooth scheme may be disconnected. Its actual clopen
integral component containing the second correspondence is used as the
normal base. Generalization lifting then applies to the genuine incidence
scheme, including any nilpotents, and gives surjectivity on each reduced
integral component onto the first support.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic

namespace FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Hom
open _root_.AlgebraicGeometry.Scheme.Products

variable {S X Y Z : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S}

/-- The target projection is locally finite type when the source is locally
finite type over the common base. -/
theorem locallyOfFiniteType_targetProjection
    (A : FiniteCorrespondenceGenerator f g) [LocallyOfFiniteType f] :
    LocallyOfFiniteType A.targetProjection := by
  have : LocallyOfFiniteType (A.targetProjection ≫ g) := by
    rw [← A.projection_base]
    infer_instance
  exact locallyOfFiniteType_of_comp A.targetProjection g

/-- Every genuine incidence projection over a smooth intermediate scheme
is generalizing, with no global integrality hypothesis on that scheme. -/
theorem generalizingMap_incidenceFst_smooth
    (k : Type u) [Field k]
    {X Y Z : SmoothSite (Spec (.of k))}
    (A : FiniteCorrespondenceGenerator X.hom Y.hom)
    (B : FiniteCorrespondenceGenerator Y.hom Z.hom) :
    GeneralizingMap (A.incidenceFst B) := by
  have := A.locallyOfFiniteType_targetProjection
  have : IsNoetherian ((𝟭 Scheme).obj Y.left) :=
    inferInstanceAs (IsNoetherian Y.left)
  exact generalizingMap_of_isPullback_component _ _ _ _ (.of_hasPullback _ _)
    B.range_projection_mem (fun y ↦
      ⟨SmoothSite.isDomain_stalk k Y y, SmoothSite.isIntegrallyClosed_stalk k Y y⟩)

/-- Each reduced integral component of genuine smooth-site incidence
surjects onto the first correspondence support. Empty incidence contributes
no component; neither the incidence scheme nor any smooth object is assumed integral. -/
theorem incidence_component_surjective
    (k : Type u) [Field k]
    {X Y Z : SmoothSite (Spec (.of k))}
    (A : FiniteCorrespondenceGenerator X.hom Y.hom)
    (B : FiniteCorrespondenceGenerator Y.hom Z.hom)
    (x : genericPoints (A.incidence B)) :
    Function.Surjective
      ((IntegralClosedSubscheme.pointClosure x.val).val.subschemeι ≫ A.incidenceFst B) :=
  surjective_pointClosure_of_finite_generalizing _
    (A.generalizingMap_incidenceFst_smooth k B) x.val x.property

/-- Each incidence component has exactly the specified source component of
the first generator as its image, including disconnected source schemes. -/
theorem range_incidence_component_source
    (k : Type u) [Field k]
    {X Y Z : SmoothSite (Spec (.of k))}
    (A : FiniteCorrespondenceGenerator X.hom Y.hom)
    (B : FiniteCorrespondenceGenerator Y.hom Z.hom)
    (x : genericPoints (A.incidence B)) :
    Set.range ((IntegralClosedSubscheme.pointClosure x.val).val.subschemeι ≫
      A.incidenceSource B) = Set.range A.projection := by
  rw [incidenceSource, ← Category.assoc]
  exact (A.incidence_component_surjective k B x).range_comp A.projection

/-- The actual finite image of each incidence component is an admissible
finite-correspondence generator, with component dominance now proved from
smoothness of the intermediate object. -/
noncomputable def smoothIncidenceComponentGenerator
    (k : Type u) [Field k]
    {X Y Z : SmoothSite (Spec (.of k))}
    (A : FiniteCorrespondenceGenerator X.hom Y.hom)
    (B : FiniteCorrespondenceGenerator Y.hom Z.hom)
    (x : genericPoints (A.incidence B)) :
    FiniteCorrespondenceGenerator X.hom Z.hom :=
  A.incidenceComponentImageGenerator B (A.generalizingMap_incidenceFst_smooth k B) x

/-- The admissible generator retains the literal finite-image ideal of the
reduced integral component of the actual, possibly nonreduced incidence. -/
@[simp] theorem smoothIncidenceComponentGenerator_val
    (k : Type u) [Field k]
    {X Y Z : SmoothSite (Spec (.of k))}
    (A : FiniteCorrespondenceGenerator X.hom Y.hom)
    (B : FiniteCorrespondenceGenerator Y.hom Z.hom)
    (x : genericPoints (A.incidence B)) :
    (A.smoothIncidenceComponentGenerator k B x).val =
      ((IntegralClosedSubscheme.pointClosure x.val).finiteImage (A.incidenceMap B)).val := rfl

/-- Correspondences whose intermediate images lie on different smooth
components have genuinely empty incidence. -/
theorem incidence_isEmpty_of_distinct_component
    (k : Type u) [Field k]
    {X Y Z : SmoothSite (Spec (.of k))}
    (A : FiniteCorrespondenceGenerator X.hom Y.hom)
    (B : FiniteCorrespondenceGenerator Y.hom Z.hom)
    (C : Set Y.left) (hC : C ∈ irreducibleComponents Y.left)
    (hA : Set.range A.targetProjection ⊆ C) (hne : C ≠ Set.range B.projection) :
    IsEmpty (A.incidence B) := by
  constructor
  intro w
  apply hne
  exact irreducibleComponents_eq_of_mem_of_domain_stalks
    (fun y ↦ SmoothSite.isDomain_stalk k Y y) hC B.range_projection_mem
    (hA ⟨A.incidenceFst B w, rfl⟩)
    ⟨A.incidenceSnd B w,
      (congrArg (fun e : A.incidence B ⟶ Y.left ↦ e w) (A.incidence_condition B)).symm⟩

end FiniteCorrespondenceGenerator

end Motivic
