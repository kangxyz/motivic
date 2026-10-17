/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.GraphPolynomialTor
public import Motivic.AlgebraicGeometry.Correspondences.FiniteFlatCurveFamily

/-!
# Literal triple-product coordinates for relative endpoints

The original triple product is isomorphic to the graph ambient obtained by
putting the middle-target product first. The coordinate equations below retain
the actual scheme maps for later transport of both closed support stalk actions.
No integrality of the relative base is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.RelativeEndpointDiagram

section ProductCoordinates

variable {S X M Y : Scheme.{u}} (b : X ⟶ S) (m : M ⟶ S) (y : Y ⟶ S)
  (q : M ⟶ X) (hq : q ≫ b = m)

/-- The original middle-target ambient. -/
abbrev rightAmbient := pullback m y

/-- Its actual projection to the relative source. -/
abbrev sourceProjection : rightAmbient m y ⟶ X := pullback.fst m y ≫ q

/-- Reorder the original triple product into the actual source-graph ambient. -/
def tripleToGraph : correspondenceTripleProduct b m y ⟶
    pullback (sourceProjection m y q ≫ b) b :=
  pullback.lift (pullback.snd (pullback.snd b m) (pullback.fst m y))
    (pullback.fst (pullback.snd b m) (pullback.fst m y) ≫ pullback.fst b m) (by
      dsimp only [sourceProjection]
      rw [Category.assoc, Category.assoc, hq, ← Category.assoc,
        ← pullback.condition, Category.assoc, pullback.condition])

/-- The inverse coordinate map keeps the whole original middle-target factor. -/
def graphToTriple : pullback (sourceProjection m y q ≫ b) b ⟶
    correspondenceTripleProduct b m y :=
  pullback.lift
    (pullback.lift (pullback.snd (sourceProjection m y q ≫ b) b)
      (pullback.fst (sourceProjection m y q ≫ b) b ≫ pullback.fst m y) (by
        rw [← pullback.condition]
        simp only [sourceProjection, Category.assoc, hq]))
    (pullback.fst (sourceProjection m y q ≫ b) b) (by simp)

@[reassoc (attr := simp)]
theorem tripleToGraph_fst :
    tripleToGraph b m y q hq ≫ pullback.fst (sourceProjection m y q ≫ b) b =
      pullback.snd (pullback.snd b m) (pullback.fst m y) := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem tripleToGraph_snd :
    tripleToGraph b m y q hq ≫ pullback.snd (sourceProjection m y q ≫ b) b =
      pullback.fst (pullback.snd b m) (pullback.fst m y) ≫ pullback.fst b m :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem graphToTriple_snd :
    graphToTriple b m y q hq ≫ pullback.snd (pullback.snd b m) (pullback.fst m y) =
      pullback.fst (sourceProjection m y q ≫ b) b := pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem graphToTriple_fst_fst :
    graphToTriple b m y q hq ≫ pullback.fst (pullback.snd b m) (pullback.fst m y) ≫
      pullback.fst b m = pullback.snd (sourceProjection m y q ≫ b) b := by
  simp [graphToTriple]

@[reassoc (attr := simp)]
theorem graphToTriple_fst_snd :
    graphToTriple b m y q hq ≫ pullback.fst (pullback.snd b m) (pullback.fst m y) ≫
      pullback.snd b m = pullback.fst (sourceProjection m y q ≫ b) b ≫ pullback.fst m y := by
  simp [graphToTriple]

/-- The actual triple product and graph ambient are isomorphic with the stated coordinates. -/
def tripleGraphIso : correspondenceTripleProduct b m y ≅
    pullback (sourceProjection m y q ≫ b) b where
  hom := tripleToGraph b m y q hq
  inv := graphToTriple b m y q hq
  hom_inv_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp
      · simp only [Category.assoc, graphToTriple_fst_snd, tripleToGraph_fst_assoc,
          Category.id_comp]
        exact (pullback.condition (f := pullback.snd b m) (g := pullback.fst m y)).symm
    · simp
  inv_hom_id := by
    apply pullback.hom_ext <;> simp

end ProductCoordinates

section Endpoint

variable {k : Type u} [Field k] {X : Scheme.{u}} (b : X ⟶ Spec (.of k)) (a : k)

/-- The literal relative affine line, without an integrality assumption on its base. -/
abbrev relativeLine := pullback b (FiniteFlatCurveFamily.line k).hom

/-- The actual constant section of the relative affine line. -/
def endpoint : X ⟶ relativeLine b :=
  pullback.lift (𝟙 X) (b ≫ FiniteFlatCurve.endpoint a) (by
    have he := MorphismProperty.Over.w (FiniteFlatCurveFamily.evaluationPoint k a)
    change FiniteFlatCurve.endpoint a ≫ (FiniteFlatCurveFamily.line k).hom =
      𝟙 (Spec (.of k)) at he
    simp only [Category.id_comp, Category.assoc, he, Category.comp_id])

@[reassoc (attr := simp)]
theorem endpoint_fst : endpoint b a ≫ pullback.fst b (FiniteFlatCurveFamily.line k).hom =
    𝟙 X := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem endpoint_snd : endpoint b a ≫ pullback.snd b (FiniteFlatCurveFamily.line k).hom =
    b ≫ FiniteFlatCurve.endpoint a := pullback.lift_snd _ _ _

/-- The whole relative endpoint is the actual pullback of scalar evaluation. -/
theorem endpoint_isPullback :
    IsPullback b (endpoint b a) (FiniteFlatCurve.endpoint a)
      (pullback.snd b (FiniteFlatCurveFamily.line k).hom) where
  w := (endpoint_snd b a).symm
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun s ↦ by
    have he := MorphismProperty.Over.w (FiniteFlatCurveFamily.evaluationPoint k a)
    change FiniteFlatCurve.endpoint a ≫ (FiniteFlatCurveFamily.line k).hom =
      𝟙 (Spec (.of k)) at he
    have hb : (s.snd ≫ pullback.fst b (FiniteFlatCurveFamily.line k).hom) ≫ b = s.fst := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, ← s.condition,
        Category.assoc, he, Category.comp_id]
    refine ⟨s.snd ≫ pullback.fst b (FiniteFlatCurveFamily.line k).hom, hb, ?_, ?_⟩
    · apply pullback.hom_ext
      · simp
      · change ((s.snd ≫ pullback.fst b (FiniteFlatCurveFamily.line k).hom) ≫
          endpoint b a) ≫ pullback.snd b (FiniteFlatCurveFamily.line k).hom = _
        rw [Category.assoc, endpoint_snd, ← Category.assoc, hb]
        exact s.condition
    · intro u _ hu
      have hu' := congrArg (fun q => q ≫ pullback.fst b (FiniteFlatCurveFamily.line k).hom) hu
      simpa only [PullbackCone.mk_snd, Category.assoc, endpoint_fst,
        Category.comp_id] using hu')⟩

instance endpoint_closed : IsClosedImmersion (endpoint b a) :=
  MorphismProperty.of_isPullback (endpoint_isPullback b a)
    (inferInstanceAs (IsClosedImmersion (FiniteFlatCurve.endpoint a)))

end Endpoint

end Motivic.RelativeEndpointDiagram
