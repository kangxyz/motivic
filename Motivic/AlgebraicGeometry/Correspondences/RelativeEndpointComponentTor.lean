/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.RelativeEndpointComponentDiagram

/-!
# Original component pulled-support Tor at a relative endpoint

The original left pulled ideal support maps openly to the whole endpoint
graph support; the original right pulled ideal support is isomorphic to its
product model. Their literal stalk actions therefore have the proved graph-block
Tor lengths. Point compatibilities specify where the original supports meet;
no scalar-action identification is hypothesized.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteFlatCurve

universe u

namespace Motivic.RelativeEndpointDiagram

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
  (b : X ⟶ Spec (.of k)) (y : Y ⟶ Spec (.of k)) (a : k)
  (F : FiniteCorrespondenceGenerator b (relativeLineHom b))
  (G : FiniteCorrespondenceGenerator (relativeLineHom b) y)
  (hF : F.projection ≫ endpoint b a = F.targetProjection)

/-- The whole left endpoint inclusion is closed, even for a disconnected source. -/
instance endpointLeftInclusion_closed [IsSeparated b] :
    IsClosedImmersion (endpointLeftInclusion b y a) := by
  have : IsClosedImmersion
      (Graph.morphism b (relativeLineHom b) (endpoint b a) (endpoint_base b a)) := by
    have : IsClosedImmersion
        (Graph.morphism b (relativeLineHom b) (endpoint b a) (endpoint_base b a) ≫
          pullback.fst b (relativeLineHom b)) := by
      rw [Graph.morphism_fst]
      infer_instance
    exact IsClosedImmersion.of_comp _ (pullback.fst b (relativeLineHom b))
  have he := leftSupportIso_hom_fst b (relativeLineHom b) y (endpoint b a) (endpoint_base b a)
  dsimp only [endpointLeftInclusion]
  rw [← he]
  infer_instance

/-- The whole right support product remains closed in the original triple ambient. -/
instance endpointRightInclusion_closed :
    IsClosedImmersion (endpointRightInclusion b y G.inclusion) := by
  unfold endpointRightInclusion rightSupportInclusion
  infer_instance

/-- The original left pulled ideal inclusion. -/
abbrev originalLeftInclusion :=
  (F.val.comap (pullback.fst (pullback.snd b (relativeLineHom b))
    (pullback.fst (relativeLineHom b) y))).subschemeι

/-- The original right pulled ideal inclusion. -/
abbrev originalRightInclusion :=
  (G.val.comap (pullback.snd (pullback.snd b (relativeLineHom b))
    (pullback.fst (relativeLineHom b) y))).subschemeι

variable (z : fiber (G.inclusion ≫ ambientParameter b y) a)
  (l : (F.val.comap (pullback.fst (pullback.snd b (relativeLineHom b))
    (pullback.fst (relativeLineHom b) y))).subscheme)
  (r : (G.val.comap (pullback.snd (pullback.snd b (relativeLineHom b))
    (pullback.fst (relativeLineHom b) y))).subscheme)
  (hl : originalLeftInclusion b y F l = endpointTriplePoint b y a G.inclusion z)
  (hr : originalRightInclusion b y G r = endpointTriplePoint b y a G.inclusion z)

include hF hl in
/-- Closedness identifies the actual left comparison point, including on a component. -/
theorem componentLeftToWhole_point [IsSeparated b] :
    componentLeftToWhole b y a F hF l = endpointLeftPoint b y a G.inclusion z := by
  apply (endpointLeftInclusion b y a).isClosedEmbedding.injective
  calc
    _ = originalLeftInclusion b y F l :=
      congrArg (fun q => q l) (componentLeftToWhole_inclusion b y a F hF)
    _ = endpointTriplePoint b y a G.inclusion z := hl
    _ = _ := endpointLeft_point b y a G.inclusion z

include hr in
/-- The literal original right point is the corresponding product-support graph point. -/
theorem originalRightToWhole_point :
    originalRightToWhole b y G r = endpointRightPoint b y a G.inclusion z := by
  apply (endpointRightInclusion b y G.inclusion).isClosedEmbedding.injective
  calc
    _ = originalRightInclusion b y G r :=
      congrArg (fun q => q r) (originalRightToWhole_inclusion b y G)
    _ = endpointTriplePoint b y a G.inclusion z := hr
    _ = _ := endpointRight_point b y a G.inclusion z

/-- Original ideal-support Tor in the unchanged right-source, left-coefficient order. -/
abbrev originalComponentPulledTor (n : ℕ) :=
  Intersection.pointedStalkTor (originalRightInclusion b y G) r
    (originalLeftInclusion b y F) l (endpointTriplePoint b y a G.inclusion z) hr.symm hl.symm n

include hF in
/-- The two original pulled ideal support actions have exactly the graph-block Tor length. -/
theorem originalComponentPulledTor_length [IsSeparated b] [IsOpenImmersion F.projection]
    (n : ℕ) :
    Module.length
      ((correspondenceTripleProduct b (relativeLineHom b) y).presheaf.stalk
        (endpointTriplePoint b y a G.inclusion z))
      (originalComponentPulledTor b y a F G z l r hl hr n) =
      Module.length (Graph.polynomialAmbientStalk
        (endpointAmbientSource b y) b (ambientParameter b y) a G.inclusion z)
        (Graph.polynomialTor
          (endpointAmbientSource b y) b (ambientParameter b y) a G.inclusion z n) := by
  have he := Intersection.pointedStalkTor_neighborhood_length
    (endpointRightInclusion b y G.inclusion) (endpointRightPoint b y a G.inclusion z)
    (endpointLeftInclusion b y a) (endpointLeftPoint b y a G.inclusion z)
    (endpointTriplePoint b y a G.inclusion z) (endpointRight_point b y a G.inclusion z)
    (endpointLeft_point b y a G.inclusion z)
    (originalRightInclusion b y G) r (originalLeftInclusion b y F) l
    (endpointTriplePoint b y a G.inclusion z) hr.symm hl.symm
    (originalRightToWhole b y G) (componentLeftToWhole b y a F hF) (𝟙 _)
    (by simp) (by simp)
    (originalRightToWhole_point b y a G z r hr).symm
    (componentLeftToWhole_point b y a F G hF z l hl).symm n
  exact he.symm.trans (endpointStalkTor_length b y a G.inclusion z n)

end Motivic.RelativeEndpointDiagram
