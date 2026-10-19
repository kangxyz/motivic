/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeEndpointStalkTor
public import Motivic.AlgebraicGeometry.Correspondences.Graph.Components.Composition
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Products

/-!
# Component endpoint graphs inside the whole relative endpoint

A component graph has its actual open projection to the disconnected smooth
source. Pulling that projection back gives the local-to-whole comparison of
left supports. The original incidence equations also give a morphism to the
whole endpoint fiber of the original right support.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteFlatCurve
open _root_.Motivic

universe u

namespace AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram
open _root_.AlgebraicGeometry.Scheme.SmoothSite

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
  (b : X ⟶ Spec (.of k)) (y : Y ⟶ Spec (.of k)) (a : k)
  (F : _root_.Motivic.FiniteCorrespondenceGenerator b (relativeLineHom b))
  (G : _root_.Motivic.FiniteCorrespondenceGenerator (relativeLineHom b) y)
  (hF : F.projection ≫ endpoint b a = F.targetProjection)

include hF

/-- The original graph support inclusion factors through the whole endpoint graph. -/
theorem endpointComponent_inclusion :
    F.projection ≫ Graph.morphism b (relativeLineHom b) (endpoint b a) (endpoint_base b a) =
      F.inclusion := by
  apply pullback.hom_ext
  · simp [_root_.Motivic.FiniteCorrespondenceGenerator.projection, correspondenceProjection]
  · simpa only [Category.assoc, Graph.morphism_snd] using hF

/-- The original left pulled ideal support maps to the whole endpoint-support model. -/
def componentLeftToWhole :
    (F.val.comap (pullback.fst (pullback.snd b (relativeLineHom b))
      (pullback.fst (relativeLineHom b) y))).subscheme ⟶
        leftSupport (relativeLineHom b) y (endpoint b a) :=
  (F.val.comapIso _).hom ≫
    pullback.map _ _ _ _ (𝟙 _) F.projection (𝟙 _) (by simp)
      (by simpa using (endpointComponent_inclusion b a F hF).symm) ≫
    (leftSupportIso b (relativeLineHom b) y (endpoint b a) (endpoint_base b a)).inv

instance componentLeftToWhole_isOpenImmersion [IsOpenImmersion F.projection] :
    IsOpenImmersion (componentLeftToWhole b y a F hF) := by
  unfold componentLeftToWhole
  infer_instance

/-- This open comparison preserves the original ideal-subscheme inclusion. -/
@[reassoc (attr := simp)]
theorem componentLeftToWhole_inclusion :
    componentLeftToWhole b y a F hF ≫ endpointLeftInclusion b y a =
      (F.val.comap (pullback.fst (pullback.snd b (relativeLineHom b))
        (pullback.fst (relativeLineHom b) y))).subschemeι := by
  have he := leftSupportIso_hom_fst b (relativeLineHom b) y (endpoint b a) (endpoint_base b a)
  have hinv :
      (leftSupportIso b (relativeLineHom b) y (endpoint b a) (endpoint_base b a)).inv ≫
          endpointLeftInclusion b y a =
        pullback.fst
          (pullback.fst (pullback.snd b (relativeLineHom b)) (pullback.fst (relativeLineHom b) y))
          (Graph.morphism b (relativeLineHom b) (endpoint b a) (endpoint_base b a)) := by
    dsimp only [endpointLeftInclusion]
    rw [← he, Iso.inv_hom_id_assoc]
  simp only [componentLeftToWhole, Category.assoc, hinv]
  simp [pullback.map]


/-- The original incidence lies in the literal endpoint fiber of its right support. -/
def incidenceToEndpointFiber : F.incidence G ⟶ fiber (G.inclusion ≫ ambientParameter b y) a :=
  pullback.lift (F.incidenceFst G ≫ F.projection ≫ b) (F.incidenceSnd G) (by
    change (F.incidenceFst G ≫ F.projection ≫ b) ≫ FiniteFlatCurve.endpoint a =
      F.incidenceSnd G ≫ G.projection ≫ pullback.snd b (AffineLineField.line k).hom
    calc
      _ = (F.incidenceFst G ≫ (F.projection ≫ endpoint b a)) ≫
          pullback.snd b (AffineLineField.line k).hom := by
        simp only [Category.assoc, endpoint_snd]
      _ = (F.incidenceFst G ≫ F.targetProjection) ≫
          pullback.snd b (AffineLineField.line k).hom := by rw [hF]
      _ = _ := by rw [F.incidence_condition G, Category.assoc])

@[reassoc (attr := simp)]
theorem incidenceToEndpointFiber_inclusion :
    incidenceToEndpointFiber b y a F G hF ≫ fiberInclusion (G.inclusion ≫ ambientParameter b y) a =
      F.incidenceSnd G := pullback.lift_snd _ _ _

/-- The original incidence point has exactly the retained graph coordinates. -/
@[reassoc]
theorem incidenceInclusion_graph :
    F.incidenceInclusion G ≫ (endpointAmbientIso b y).hom =
      F.incidenceSnd G ≫ G.inclusion ≫ _root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph
        (endpointAmbientSource b y) b := by
  apply pullback.hom_ext
  · simp [endpointAmbientIso, tripleGraphIso]
  · simp only [endpointAmbientIso, tripleGraphIso, Category.assoc, tripleToGraph_snd,
      _root_.Motivic.FiniteCorrespondenceGenerator.incidenceInclusion_fst_assoc,
        _root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph_snd]
    change F.incidenceFst G ≫ F.projection =
      F.incidenceSnd G ≫ G.projection ≫ pullback.fst b (AffineLineField.line k).hom
    rw [← Category.assoc, ← F.incidence_condition G, Category.assoc, ← hF, Category.assoc,
      endpoint_fst, Category.comp_id]

/-- Every actual incidence point is the triple point of its original endpoint-fiber point. -/
theorem incidence_endpointTriplePoint (w : F.incidence G) :
    endpointTriplePoint b y a G.inclusion (incidenceToEndpointFiber b y a F G hF w) =
      F.incidenceInclusion G w := by
  have hz : Graph.cutPoint (ambientParameter b y) a G.inclusion
      (incidenceToEndpointFiber b y a F G hF w) = F.incidenceSnd G w :=
    congrArg (fun q => q w) (incidenceToEndpointFiber_inclusion b y a F G hF)
  change (endpointAmbientIso b y).inv
    (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph (endpointAmbientSource b y) b
      (G.inclusion _)) = _
  rw [hz]
  have he := congrArg (fun q => q w) (incidenceInclusion_graph b y a F G hF)
  change (endpointAmbientIso b y).hom (F.incidenceInclusion G w) =
    _root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph (endpointAmbientSource b y) b
      (G.inclusion (F.incidenceSnd G w)) at he
  rw [← he]
  exact congrArg (fun q => q (F.incidenceInclusion G w)) (endpointAmbientIso b y).hom_inv_id

omit hF

/-- The original right pulled ideal support is isomorphic to its actual product model. -/
def originalRightToWhole :
    (G.val.comap (pullback.snd (pullback.snd b (relativeLineHom b))
      (pullback.fst (relativeLineHom b) y))).subscheme ⟶
      rightSupportProduct b (relativeLineHom b) y
        (pullback.fst b (AffineLineField.line k).hom) G.inclusion :=
  (G.val.comapIso _).hom ≫
    (rightSupportIso b (relativeLineHom b) y
      (pullback.fst b (AffineLineField.line k).hom) rfl G.inclusion).inv

instance originalRightToWhole_isIso : IsIso (originalRightToWhole b y G) := by
  unfold originalRightToWhole
  infer_instance

/-- The right isomorphism preserves the literal original ideal-subscheme inclusion. -/
@[reassoc (attr := simp)]
theorem originalRightToWhole_inclusion :
    originalRightToWhole b y G ≫ endpointRightInclusion b y G.inclusion =
      (G.val.comap (pullback.snd (pullback.snd b (relativeLineHom b))
        (pullback.fst (relativeLineHom b) y))).subschemeι := by
  have he := rightSupportIso_hom_fst b (relativeLineHom b) y
    (pullback.fst b (AffineLineField.line k).hom) rfl G.inclusion
  have hinv :
      (rightSupportIso b (relativeLineHom b) y
          (pullback.fst b (AffineLineField.line k).hom) rfl G.inclusion).inv ≫
        endpointRightInclusion b y G.inclusion =
      pullback.fst
        (pullback.snd (pullback.snd b (relativeLineHom b)) (pullback.fst (relativeLineHom b) y))
        G.inclusion := by
    dsimp only [endpointRightInclusion]
    rw [← he, Iso.inv_hom_id_assoc]
  simp only [originalRightToWhole, Category.assoc, hinv]
  simp

end AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram

namespace AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram
open _root_.AlgebraicGeometry.Scheme.SmoothSite

variable {k : Type u} [Field k] (X Y : SmoothSite (Spec (.of k)))
  (a : k) (E : Set X.left) (hE : E ∈ irreducibleComponents X.left)

/-- The actual endpoint graph component on an arbitrary, possibly disconnected smooth source. -/
abbrev endpointComponentGenerator :
    _root_.Motivic.FiniteCorrespondenceGenerator X.hom (relativeLineHom X.hom) :=
  componentGraphGeneratorOver (X := X.left)
    (Y := (SmoothSite.product X (AffineLineField.line k)).left)
    (endpoint X.hom a) (endpoint_base X.hom a) E hE

instance endpointComponentGenerator_projection_open :
    IsOpenImmersion (endpointComponentGenerator X a E hE).projection :=
  SmoothSite.componentGraphGeneratorOver_projection_isOpenImmersion k
    (X := X) (Y := SmoothSite.product X (AffineLineField.line k))
    (endpoint X.hom a) (endpoint_base X.hom a) E hE

/-- Its endpoint factorization is supplied by the proved component-graph geometry. -/
theorem endpointComponentGenerator_target :
    (endpointComponentGenerator X a E hE).projection ≫ endpoint X.hom a =
      (endpointComponentGenerator X a E hE).targetProjection :=
  componentGraphGeneratorOver_projection_target (X := X.left)
    (Y := (SmoothSite.product X (AffineLineField.line k)).left)
    (endpoint X.hom a) (endpoint_base X.hom a) E hE

/-- The component-to-whole left comparison is genuinely open for every smooth component. -/
theorem endpointComponent_left_open :
    IsOpenImmersion (componentLeftToWhole X.hom Y.hom a (endpointComponentGenerator X a E hE)
      (endpointComponentGenerator_target X a E hE)) := inferInstance

/-- Direct componentwise use of the whole original endpoint-fiber point identity. -/
theorem endpointComponent_incidence_point
    (G : _root_.Motivic.FiniteCorrespondenceGenerator (relativeLineHom X.hom) Y.hom)
    (w : (endpointComponentGenerator X a E hE).incidence G) :
    endpointTriplePoint X.hom Y.hom a G.inclusion
      (incidenceToEndpointFiber X.hom Y.hom a (endpointComponentGenerator X a E hE) G
        (endpointComponentGenerator_target X a E hE) w) =
      (endpointComponentGenerator X a E hE).incidenceInclusion G w :=
  incidence_endpointTriplePoint X.hom Y.hom a (endpointComponentGenerator X a E hE) G
    (endpointComponentGenerator_target X a E hE) w

end AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram
