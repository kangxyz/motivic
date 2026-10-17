/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.RelativeEndpointDiagram

/-!
# Original support pullbacks in relative endpoint coordinates

The right support pulled into the original triple product is the actual closed
support product in graph coordinates. The Cartesian square and isomorphism
record the original inclusion map, for later stalk-action transport.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.RelativeEndpointDiagram

variable {S X M Y C : Scheme.{u}} (b : X ⟶ S) (m : M ⟶ S) (y : Y ⟶ S)
  (q : M ⟶ X) (hq : q ≫ b = m) (j : C ⟶ rightAmbient m y)

/-- The original closed support times the relative source in graph coordinates. -/
abbrev rightSupportProduct := pullback ((j ≫ sourceProjection m y q) ≫ b) b

/-- Its actual map into the original triple product. -/
def rightSupportInclusion : rightSupportProduct b m y q j ⟶
    correspondenceTripleProduct b m y :=
  Graph.supportProductMap (sourceProjection m y q) b j ≫ (tripleGraphIso b m y q hq).inv

@[reassoc (attr := simp)]
theorem rightSupportInclusion_snd :
    rightSupportInclusion b m y q hq j ≫
      pullback.snd (pullback.snd b m) (pullback.fst m y) =
        pullback.fst ((j ≫ sourceProjection m y q) ≫ b) b ≫ j := by
  simp [rightSupportInclusion, tripleGraphIso, Graph.supportProductMap, pullback.map]

/-- The support-product map is the actual base change of the original support inclusion. -/
theorem rightSupport_productSquare :
    IsPullback (Graph.supportProductMap (sourceProjection m y q) b j)
      (pullback.fst ((j ≫ sourceProjection m y q) ≫ b) b)
      (pullback.fst (sourceProjection m y q ≫ b) b) j := by
  apply IsPullback.flip
  refine IsPullback.of_bot
    (t := IsPullback.of_hasPullback (sourceProjection m y q ≫ b) b) ?_ ?_
  · simpa only [Graph.supportProductMap, pullback.map, pullback.lift_snd,
      Category.comp_id, Category.assoc] using
      (IsPullback.of_hasPullback ((j ≫ sourceProjection m y q) ≫ b) b)
  · simp [Graph.supportProductMap, pullback.map]

/-- Reordering the ambient identifies the whole right pulled support by a
Cartesian square. No reduction, integrality, or flatness is required. -/
theorem rightSupport_isPullback :
    IsPullback (rightSupportInclusion b m y q hq j)
      (pullback.fst ((j ≫ sourceProjection m y q) ≫ b) b)
      (pullback.snd (pullback.snd b m) (pullback.fst m y)) j := by
  apply (rightSupport_productSquare b m y q j).of_iso
    (Iso.refl _) (tripleGraphIso b m y q hq).symm (Iso.refl _) (Iso.refl _)
  · simp [rightSupportInclusion]
  · simp
  · simp [tripleGraphIso]
  · simp

/-- The canonical isomorphism to the whole original right support pullback. -/
def rightSupportIso : rightSupportProduct b m y q j ≅
    pullback (pullback.snd (pullback.snd b m) (pullback.fst m y)) j :=
  (rightSupport_isPullback b m y q hq j).isoPullback

@[reassoc (attr := simp)]
theorem rightSupportIso_hom_fst :
    (rightSupportIso b m y q hq j).hom ≫
      pullback.fst (pullback.snd (pullback.snd b m) (pullback.fst m y)) j =
        rightSupportInclusion b m y q hq j :=
  (rightSupport_isPullback b m y q hq j).isoPullback_hom_fst

@[reassoc (attr := simp)]
theorem rightSupportIso_hom_snd :
    (rightSupportIso b m y q hq j).hom ≫
      pullback.snd (pullback.snd (pullback.snd b m) (pullback.fst m y)) j =
        pullback.fst ((j ≫ sourceProjection m y q) ≫ b) b :=
  (rightSupport_isPullback b m y q hq j).isoPullback_hom_snd

section LeftSupport

variable (e : X ⟶ M) (he : e ≫ m = b)

/-- The original middle-target factor pulled back along the entire source section. -/
abbrev leftSupport := pullback e (pullback.fst m y)

/-- Its literal inclusion into the original triple ambient. -/
def leftSupportInclusion : leftSupport m y e ⟶ correspondenceTripleProduct b m y :=
  pullback.lift
    (pullback.fst e (pullback.fst m y) ≫ Graph.morphism b m e he)
    (pullback.snd e (pullback.fst m y)) (by
      simp only [Category.assoc, Graph.morphism_snd]
      exact pullback.condition)

@[reassoc (attr := simp)]
theorem leftSupportInclusion_fst :
    leftSupportInclusion b m y e he ≫
      pullback.fst (pullback.snd b m) (pullback.fst m y) =
        pullback.fst e (pullback.fst m y) ≫ Graph.morphism b m e he :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem leftSupportInclusion_snd :
    leftSupportInclusion b m y e he ≫
      pullback.snd (pullback.snd b m) (pullback.fst m y) =
        pullback.snd e (pullback.fst m y) := pullback.lift_snd _ _ _

/-- The entire section graph pulled into the triple product has this Cartesian model. -/
theorem leftSupport_isPullback :
    IsPullback (leftSupportInclusion b m y e he)
      (pullback.fst e (pullback.fst m y))
      (pullback.fst (pullback.snd b m) (pullback.fst m y)) (Graph.morphism b m e he) := by
  refine IsPullback.of_right
    (t := (IsPullback.of_hasPullback (pullback.snd b m) (pullback.fst m y)).flip) ?_
    (leftSupportInclusion_fst b m y e he)
  simpa only [leftSupportInclusion_snd, Graph.morphism_snd] using
    (IsPullback.of_hasPullback e (pullback.fst m y)).flip

/-- The canonical isomorphism retains the whole original left graph support pullback. -/
def leftSupportIso : leftSupport m y e ≅
    pullback (pullback.fst (pullback.snd b m) (pullback.fst m y)) (Graph.morphism b m e he) :=
  (leftSupport_isPullback b m y e he).isoPullback

@[reassoc (attr := simp)]
theorem leftSupportIso_hom_fst :
    (leftSupportIso b m y e he).hom ≫
      pullback.fst (pullback.fst (pullback.snd b m) (pullback.fst m y))
        (Graph.morphism b m e he) = leftSupportInclusion b m y e he :=
  (leftSupport_isPullback b m y e he).isoPullback_hom_fst

/-- After the literal ambient reordering, the section graph is exactly the
source graph restricted to its original pullback; the two coordinates are unchanged. -/
@[reassoc]
theorem leftSupportInclusion_graph (hsection : e ≫ q = 𝟙 X) :
    leftSupportInclusion b m y e he ≫ (tripleGraphIso b m y q hq).hom =
      pullback.snd e (pullback.fst m y) ≫ correspondenceGraph (sourceProjection m y q) b := by
  apply pullback.hom_ext
  · simp [tripleGraphIso]
  · simp only [tripleGraphIso, Category.assoc, tripleToGraph_snd,
      leftSupportInclusion_fst_assoc, Graph.morphism_fst, Category.comp_id,
      correspondenceGraph_snd, sourceProjection]
    rw [← Category.assoc, ← pullback.condition, Category.assoc, hsection, Category.comp_id]

end LeftSupport

section EndpointFiber

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
  (b : X ⟶ Spec (.of k)) (y : Y ⟶ Spec (.of k)) (a : k)

/-- The original structural map on the relative affine line. -/
abbrev relativeLineHom : relativeLine b ⟶ Spec (.of k) :=
  pullback.fst b (FiniteFlatCurveFamily.line k).hom ≫ b

/-- The original parameter of the whole middle-target ambient. -/
abbrev ambientParameter : rightAmbient (relativeLineHom b) y ⟶ Spec (.of (Polynomial k)) :=
  pullback.fst (relativeLineHom b) y ≫ pullback.snd b (FiniteFlatCurveFamily.line k).hom

/-- The relative endpoint respects its original structural map. -/
theorem endpoint_base : endpoint b a ≫ relativeLineHom b = b := by
  simp [relativeLineHom]

/-- Pasting the actual relative endpoint square retains the entire ambient fiber. -/
theorem leftEndpoint_fiberSquare :
    IsPullback
      (pullback.fst (endpoint b a) (pullback.fst (relativeLineHom b) y) ≫ b)
      (pullback.snd (endpoint b a) (pullback.fst (relativeLineHom b) y))
      (FiniteFlatCurve.endpoint a) (ambientParameter b y) :=
  (IsPullback.of_hasPullback (endpoint b a) (pullback.fst (relativeLineHom b) y)).paste_horiz
    (endpoint_isPullback b a)

/-- The left endpoint support is the whole original parameter fiber. -/
def leftEndpointFiberIso : leftSupport (relativeLineHom b) y (endpoint b a) ≅
    FiniteFlatCurve.fiber (ambientParameter b y) a :=
  (leftEndpoint_fiberSquare b y a).isoPullback

@[reassoc (attr := simp)]
theorem leftEndpointFiberIso_hom_inclusion :
    (leftEndpointFiberIso b y a).hom ≫
      FiniteFlatCurve.fiberInclusion (ambientParameter b y) a =
        pullback.snd (endpoint b a) (pullback.fst (relativeLineHom b) y) :=
  (leftEndpoint_fiberSquare b y a).isoPullback_hom_snd

/-- The literal graph-then-endpoint source inclusion in the graph ambient. -/
@[reassoc]
theorem leftEndpointInclusion_graph :
    leftSupportInclusion b (relativeLineHom b) y (endpoint b a) (endpoint_base b a) ≫
        (tripleGraphIso b (relativeLineHom b) y
          (pullback.fst b (FiniteFlatCurveFamily.line k).hom) rfl).hom =
      (leftEndpointFiberIso b y a).hom ≫
        FiniteFlatCurve.fiberInclusion (ambientParameter b y) a ≫
          correspondenceGraph
            (sourceProjection (relativeLineHom b) y
              (pullback.fst b (FiniteFlatCurveFamily.line k).hom)) b := by
  rw [← Category.assoc, leftEndpointFiberIso_hom_inclusion]
  exact leftSupportInclusion_graph b (relativeLineHom b) y
    (pullback.fst b (FiniteFlatCurveFamily.line k).hom) rfl
    (endpoint b a) (endpoint_base b a) (endpoint_fst b a)

end EndpointFiber

end Motivic.RelativeEndpointDiagram
