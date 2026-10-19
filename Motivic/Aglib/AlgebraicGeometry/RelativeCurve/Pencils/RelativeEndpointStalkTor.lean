/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeEndpointSupportDiagram
public import Motivic.Aglib.AlgebraicGeometry.Intersection.PointedStalkTor

/-!
# Literal relative-endpoint intersection stalk Tor

The actual support pullback diagrams transport the original two stalk actions
into the graph-plus-parameter calculation. The endpoint and coefficient maps
are literal scheme maps, and all point identifications are proved from their
commuting squares. The entire endpoint support is retained.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteFlatCurve

universe u

namespace AlgebraicGeometry.Scheme.Graph

variable {k : Type u} [Field k] {C P X : Scheme.{u}}
  (h : P ⟶ X) (b : X ⟶ Spec (.of k))
  (f : P ⟶ Spec (.of (Polynomial k))) (a : k) (j : C ⟶ P)
  (z : fiber (j ≫ f) a)

/-- The original endpoint source followed by the smooth source graph. -/
abbrev polynomialSourceInclusion := fiberInclusion f a ≫
  _root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph h b

/-- The common graph point is the actual image of the whole endpoint source. -/
theorem polynomialSource_point :
    _root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph h b (j (cutPoint f a j z)) =
      polynomialSourceInclusion h b f a (fiberMap f a j z) := by
  exact congrArg (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph h b)
    (congrArg (fun q : fiber (j ≫ f) a ⟶ P => q z) (fiberMap_inclusion f a j)).symm

/-- The same graph point is the actual image of the original coefficient support product. -/
theorem polynomialCoefficient_point :
    _root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph h b (j (cutPoint f a j z)) =
      supportProductMap h b j (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph (j ≫ h) b
        (cutPoint f a j z)) :=
  (congrArg (fun q : C ⟶ pullback (h ≫ b) b => q (cutPoint f a j z))
    (supportProductMap_graph h b j)).symm

/-- The two-stage endpoint stalk action is precisely the original composite
scheme map's pointed stalk action. -/
theorem graphEndpointStalkMap_eq_pointed :
    graphEndpointStalkMap h b f a j z =
      StalkTransport.pointedMap (polynomialSourceInclusion h b f a) (fiberMap f a j z)
        (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph h b (j (cutPoint f a j z)))
        (polynomialSource_point h b f a j z) := by
  unfold graphEndpointStalkMap endpointSourceStalkMap
  rw [← StalkTransport.pointedMap_image (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph
    h b)]
  exact StalkTransport.pointedMap_comp _ _ _ _ _ _ _

/-- The graph-block Tor is the actual intersection Tor of the two literal
scheme maps, with the original coefficient-first factor order. -/
theorem polynomialTor_eq_pointed (n : ℕ) :
    polynomialTor h b f a j z n =
      Intersection.pointedStalkTor
        (polynomialSourceInclusion h b f a) (fiberMap f a j z)
        (supportProductMap h b j) (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph (j ≫
          h) b (cutPoint f a j z))
        (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph h b (j (cutPoint f a j z)))
        (polynomialSource_point h b f a j z) (polynomialCoefficient_point h b f a j z) n := by
  unfold polynomialTor Intersection.pointedStalkTor
  rw [graphEndpointStalkMap_eq_pointed]
  rfl

end AlgebraicGeometry.Scheme.Graph

namespace AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram
open _root_.AlgebraicGeometry.Scheme.SmoothSite

variable {k : Type u} [Field k] {X Y C : Scheme.{u}}
  (b : X ⟶ Spec (.of k)) (y : Y ⟶ Spec (.of k)) (a : k)
  (j : C ⟶ rightAmbient (relativeLineHom b) y)

/-- The source projection from the entire original middle-target ambient. -/
abbrev endpointAmbientSource :=
  sourceProjection (relativeLineHom b) y (pullback.fst b (AffineLineField.line k).hom)

/-- The actual triple-to-graph ambient isomorphism for this relative endpoint. -/
abbrev endpointAmbientIso :=
  tripleGraphIso b (relativeLineHom b) y (pullback.fst b (AffineLineField.line k).hom) rfl

/-- The original whole left endpoint-support inclusion in the triple product. -/
abbrev endpointLeftInclusion :=
  leftSupportInclusion b (relativeLineHom b) y (endpoint b a) (endpoint_base b a)

/-- The original whole right support inclusion in the triple product. -/
abbrev endpointRightInclusion :=
  rightSupportInclusion b (relativeLineHom b) y
    (pullback.fst b (AffineLineField.line k).hom) rfl j

/-- The source square commutes before taking any stalk. -/
theorem endpointLeft_inverse_square :
    (leftEndpointFiberIso b y a).inv ≫ endpointLeftInclusion b y a =
      Graph.polynomialSourceInclusion (endpointAmbientSource b y) b (ambientParameter b y) a ≫
        (endpointAmbientIso b y).inv := by
  apply (cancel_epi (leftEndpointFiberIso b y a).hom).mp
  simp only [Iso.hom_inv_id_assoc]
  apply (cancel_mono (endpointAmbientIso b y).hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    leftEndpointInclusion_graph b y a

/-- The right support square also commutes by its original definition. -/
theorem endpointRight_inverse_square :
    endpointRightInclusion b y j =
      Graph.supportProductMap (endpointAmbientSource b y) b j ≫ (endpointAmbientIso b y).inv := rfl

variable (z : fiber (j ≫ ambientParameter b y) a)

/-- The actual left endpoint-support point before changing ambient coordinates. -/
abbrev endpointLeftPoint :=
  (leftEndpointFiberIso b y a).inv (fiberMap (ambientParameter b y) a j z)

/-- The actual point of the whole right support product. -/
abbrev endpointRightPoint :=
  _root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph (j ≫ endpointAmbientSource b y) b
    (Graph.cutPoint (ambientParameter b y) a j z)

/-- The original triple ambient point, with all coordinates retained. -/
abbrev endpointTriplePoint :=
  (endpointAmbientIso b y).inv
    (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph (endpointAmbientSource b y) b
      (j (Graph.cutPoint (ambientParameter b y) a j z)))

/-- The triple point is the image of the actual left support point. -/
theorem endpointLeft_point :
    endpointTriplePoint b y a j z = endpointLeftInclusion b y a (endpointLeftPoint b y a j z) := by
  calc
    _ = (endpointAmbientIso b y).inv
        (Graph.polynomialSourceInclusion (endpointAmbientSource b y) b (ambientParameter b y) a
          (fiberMap (ambientParameter b y) a j z)) :=
      congrArg (endpointAmbientIso b y).inv
        (Graph.polynomialSource_point (endpointAmbientSource b y) b (ambientParameter b y) a j z)
    _ = _ := (congrArg (fun q => q (fiberMap (ambientParameter b y) a j z))
      (endpointLeft_inverse_square b y a)).symm

/-- The same original triple point is the image of the actual right support point. -/
theorem endpointRight_point :
    endpointTriplePoint b y a j z = endpointRightInclusion b y j (endpointRightPoint b y a j z) :=
  congrArg (endpointAmbientIso b y).inv
    (Graph.polynomialCoefficient_point (endpointAmbientSource b y) b (ambientParameter b y) a j z)

/-- The original triple-support Tor in the right-source, left-coefficient order
used by the four-factor incidence comparison. -/
abbrev endpointStalkTor (n : ℕ) :=
  Intersection.pointedStalkTor
    (endpointRightInclusion b y j) (endpointRightPoint b y a j z)
    (endpointLeftInclusion b y a) (endpointLeftPoint b y a j z)
    (endpointTriplePoint b y a j z) (endpointRight_point b y a j z)
    (endpointLeft_point b y a j z) n

/-- Both literal support scalar actions transport to the graph calculation.
The original reversed Tor order is changed by the proved balance isomorphism. -/
theorem endpointStalkTor_length (n : ℕ) :
    Module.length
      ((correspondenceTripleProduct b (relativeLineHom b) y).presheaf.stalk
        (endpointTriplePoint b y a j z)) (endpointStalkTor b y a j z n) =
      Module.length
        (Graph.polynomialAmbientStalk (endpointAmbientSource b y) b (ambientParameter b y) a j z)
        (Graph.polynomialTor (endpointAmbientSource b y) b (ambientParameter b y) a j z n) := by
  rw [endpointStalkTor, Intersection.pointedStalkTor_balance_length]
  have he := Intersection.pointedStalkTor_neighborhood_length
    (endpointLeftInclusion b y a) (endpointLeftPoint b y a j z)
    (endpointRightInclusion b y j) (endpointRightPoint b y a j z)
    (endpointTriplePoint b y a j z) (endpointLeft_point b y a j z)
    (endpointRight_point b y a j z)
    (Graph.polynomialSourceInclusion (endpointAmbientSource b y) b (ambientParameter b y) a)
    (fiberMap (ambientParameter b y) a j z)
    (Graph.supportProductMap (endpointAmbientSource b y) b j) (endpointRightPoint b y a j z)
    (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph (endpointAmbientSource b y) b
      (j (Graph.cutPoint (ambientParameter b y) a j z)))
    (Graph.polynomialSource_point (endpointAmbientSource b y) b (ambientParameter b y) a j z)
    (Graph.polynomialCoefficient_point (endpointAmbientSource b y) b (ambientParameter b y) a j z)
    (leftEndpointFiberIso b y a).inv (𝟙 _) (endpointAmbientIso b y).inv
    (endpointLeft_inverse_square b y a) (by simp [endpointRight_inverse_square]) rfl rfl n
  rw [← Graph.polynomialTor_eq_pointed] at he
  exact he

/-- The actual original triple-support Tor retains precisely the original
closed-support endpoint Koszul complex. The whole support may be nonreduced. -/
theorem endpointStalkTor_koszul_length [Smooth b] [IsSeparated b] [Flat y]
    [IsClosedImmersion j] (n : ℕ) :
    Module.length
      ((correspondenceTripleProduct b (relativeLineHom b) y).presheaf.stalk
        (endpointTriplePoint b y a j z)) (endpointStalkTor b y a j z n) =
      Module.length (C.presheaf.stalk (Graph.cutPoint (ambientParameter b y) a j z))
        ((_root_.ChainComplex.Koszul.coefficientComplex
          (ModuleCat.of (C.presheaf.stalk (Graph.cutPoint (ambientParameter b y) a j z))
            (C.presheaf.stalk (Graph.cutPoint (ambientParameter b y) a j z)))
          [scalar (j ≫ ambientParameter b y) a
            (Graph.cutPoint (ambientParameter b y) a j z)]).homology n) := by
  rw [endpointStalkTor_length]
  exact Graph.polynomialTor_length (endpointAmbientSource b y) b (ambientParameter b y) a j z n

end AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram
