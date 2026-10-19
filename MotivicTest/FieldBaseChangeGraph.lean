/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.BaseChange.Field.Graph

/-!
# Whole-graph consumers for arbitrary field change

No connectedness, irreducibility, or finite-extension hypothesis occurs.
The source of a single original graph component may split after extension;
the proved partition enumerates every resulting component exactly once.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.AlgebraicGeometry.Scheme (genericMultiplicity genericMultiplicity_eq_one)
open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

namespace MotivicTest.FieldBaseChangeGraph
open _root_.AlgebraicGeometry.Scheme (SmoothSite)

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L)
  {X Y : SmoothSite.overField k} (f : X ⟶ Y)

local instance fieldBaseChangeGraph_test_isNoetherian_idObj (U : SmoothSite.overField k) :
    IsNoetherian ((𝟭 Scheme).obj U.left) :=
  inferInstanceAs (IsNoetherian U.left)

local instance fieldBaseChangeGraph_test_isReduced_idObj (U : SmoothSite.overField k) :
    IsReduced ((𝟭 Scheme).obj U.left) :=
  inferInstanceAs (IsReduced U.left)

/-- Every possibly split whole graph component is reduced. -/
example (C : Set X.left) (hC : C ∈ irreducibleComponents X.left) :
    IsReduced ((componentGraphGeneratorOver f.left (MorphismProperty.Over.w f)
      C hC).fieldBaseChangeSupport φ) := inferInstance

/-- Its coefficient is one because the whole new graph support is reduced. -/
theorem actualGraphMultiplicity (C : Set X.left) (hC : C ∈ irreducibleComponents X.left)
    (w : genericPoints ((componentGraphGeneratorOver f.left (MorphismProperty.Over.w f)
      C hC).fieldBaseChangeSupport φ)) : genericMultiplicity w = 1 :=
  genericMultiplicity_eq_one w

/-- Every new source generic occurs once, including branches of one original component. -/
def actualGraphComponentPartition : Motivic.FieldBaseChangeGraph.ComponentIndex φ f ≃
    genericPoints ((SmoothSite.fieldBaseChange φ).obj X).left :=
  Motivic.FieldBaseChangeGraph.sourceGenericEquiv φ f

/-- Field change preserves the actual full graph cycle of an arbitrary smooth-site map. -/
theorem wholeGraphPreserved :
    FiniteCorrespondence.fieldBaseChange (X := X) (Y := Y) φ
        (componentGraphCycleOver f.left (MorphismProperty.Over.w f)) =
      componentGraphCycleOver ((SmoothSite.fieldBaseChange φ).map f).left
        (MorphismProperty.Over.w ((SmoothSite.fieldBaseChange φ).map f)) :=
  FiniteCorrespondence.fieldBaseChange_componentGraphCycleOver φ f

/-- The existing graph functor's exact morphisms satisfy the graph equality. -/
theorem actualGraphFunctorMaps :
    FiniteCorrespondence.fieldBaseChange (X := X) (Y := Y) φ ((Cor.graphFunctor k).map f) =
      (Cor.graphFunctor L).map ((SmoothSite.fieldBaseChange φ).map f) :=
  FiniteCorrespondence.fieldBaseChange_componentGraphCycleOver φ f

/-- The complete identity cycle on a disconnected or empty source is preserved. -/
theorem actualIdentityPreserved (X : SmoothSite.overField k) :
    FiniteCorrespondence.fieldBaseChange (X := X) (Y := X) φ (componentIdentityCycle X.hom) =
      componentIdentityCycle ((SmoothSite.fieldBaseChange φ).obj X).hom :=
  FiniteCorrespondence.fieldBaseChange_componentIdentityCycle φ X

/-- Signed integer multiples of the whole graph are preserved as well. -/
theorem signedWholeGraphPreserved (n : ℤ) :
    FiniteCorrespondence.fieldBaseChange (X := X) (Y := Y) φ
        (n • componentGraphCycleOver f.left (MorphismProperty.Over.w f)) =
      n • componentGraphCycleOver ((SmoothSite.fieldBaseChange φ).map f).left
        (MorphismProperty.Over.w ((SmoothSite.fieldBaseChange φ).map f)) := by
  rw [map_zsmul, wholeGraphPreserved]

open Lean in
run_cmd do
  for name in #[``FiniteCorrespondenceGenerator.fieldBaseChangeProjection_range,
      ``FiniteCorrespondenceGenerator.fieldBaseChangeInclusion_graph,
      ``fieldBaseChangeGraphProjection_isOpenImmersion,
      ``fieldBaseChangeGraphSupport_isReduced,
      ``fieldBaseChangeComponentGenerator_componentGraph,
      ``Motivic.FieldBaseChangeGraph.sourceGenericEquiv,
      ``FiniteCorrespondence.fieldBaseChange_componentGraphCycleOver,
      ``FiniteCorrespondence.fieldBaseChange_componentIdentityCycle,
      ``actualGraphMultiplicity, ``actualGraphComponentPartition, ``wholeGraphPreserved,
      ``actualGraphFunctorMaps, ``actualIdentityPreserved, ``signedWholeGraphPreserved] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual whole-graph field change uses only standard foundations."

end MotivicTest.FieldBaseChangeGraph
