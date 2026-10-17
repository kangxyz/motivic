/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.RelativeEndpointComponentTor
public import Motivic.AlgebraicGeometry.Correspondences.GlobalIncidenceAmbientTorComparison
public import Motivic.AlgebraicGeometry.Correspondences.TripleGenericDominance

/-!
# Actual four-factor incidence Tor for relative endpoint components

The original four-factor incidence modules are compared with their original
pulled ideal supports, then with the literal graph-plus-parameter calculation.
Every point and scalar compatibility is supplied by the actual incidence and
support maps. The smooth source may be disconnected; only the selected open
component graph is used locally. No right-support projection flatness is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteFlatCurve

universe u

namespace Motivic.RelativeEndpointDiagram

open GlobalIncidenceAmbientTorComparison

variable {k : Type u} [Field k] (X Y : SmoothSite (Spec (.of k)))
  (a : k) (E : Set X.left) (hE : E ∈ irreducibleComponents X.left)
  (G : FiniteCorrespondenceGenerator (relativeLineHom X.hom) Y.hom)

/-- The actual whole right-support endpoint point determined by a component incidence. -/
abbrev componentEndpointPoint (w : (endpointComponentGenerator X a E hE).incidence G) :=
  incidenceToEndpointFiber X.hom Y.hom a (endpointComponentGenerator X a E hE) G
    (endpointComponentGenerator_target X a E hE) w

/-- The actual four-factor Tor has precisely the graph-block Tor length, with
both original scalar actions and the proved factor exchange retained. -/
theorem component_incidenceTor_graph_length
    (w : (endpointComponentGenerator X a E hE).incidence G) (n : ℕ) :
    Module.length ((endpointComponentGenerator X a E hE).incidenceAmbientStalk G w)
      ((endpointComponentGenerator X a E hE).incidenceTor G w n) =
      Module.length
        (Graph.polynomialAmbientStalk (endpointAmbientSource X.hom Y.hom) X.hom
          (ambientParameter X.hom Y.hom) a G.inclusion (componentEndpointPoint X Y a E hE G w))
        (Graph.polynomialTor (endpointAmbientSource X.hom Y.hom) X.hom
          (ambientParameter X.hom Y.hom) a G.inclusion
          (componentEndpointPoint X Y a E hE G w) n) := by
  let F := endpointComponentGenerator X a E hE
  let z := componentEndpointPoint X Y a E hE G w
  have hl : originalLeftInclusion X.hom Y.hom F (toLeftPulled F G w) =
      endpointTriplePoint X.hom Y.hom a G.inclusion z :=
    (congrArg (fun q => q w) (toLeftPulled_inclusion F G)).trans
      (endpointComponent_incidence_point X Y a E hE G w).symm
  have hr : originalRightInclusion X.hom Y.hom G (toRightPulled F G w) =
      endpointTriplePoint X.hom Y.hom a G.inclusion z :=
    (congrArg (fun q => q w) (toRightPulled_inclusion F G)).trans
      (endpointComponent_incidence_point X Y a E hE G w).symm
  have ha := Intersection.pointedStalkTor_length
    (originalRightInclusion X.hom Y.hom G) (toRightPulled F G w)
    (originalLeftInclusion X.hom Y.hom F) (toLeftPulled F G w)
    (endpointTriplePoint X.hom Y.hom a G.inclusion z) hr.symm hl.symm n
  have hb := originalComponentPulledTor_length X.hom Y.hom a F G
    (endpointComponentGenerator_target X a E hE) z
    (toLeftPulled F G w) (toRightPulled F G w) hl hr n
  exact (incidenceTor_length_eq_pulled k F G w n).trans (ha.symm.trans hb)

/-- The original four-factor incidence Tor is the singleton endpoint Koszul
homology length on the original right support, in every degree. -/
theorem component_incidenceTor_koszul_length
    (w : (endpointComponentGenerator X a E hE).incidence G) (n : ℕ) :
    Module.length ((endpointComponentGenerator X a E hE).incidenceAmbientStalk G w)
      ((endpointComponentGenerator X a E hE).incidenceTor G w n) =
      Module.length (G.scheme.presheaf.stalk
          (Graph.cutPoint (ambientParameter X.hom Y.hom) a G.inclusion
            (componentEndpointPoint X Y a E hE G w)))
        ((Koszul.coefficientComplex
          (ModuleCat.of (G.scheme.presheaf.stalk
            (Graph.cutPoint (ambientParameter X.hom Y.hom) a G.inclusion
              (componentEndpointPoint X Y a E hE G w)))
            (G.scheme.presheaf.stalk
              (Graph.cutPoint (ambientParameter X.hom Y.hom) a G.inclusion
                (componentEndpointPoint X Y a E hE G w))))
          [scalar (G.inclusion ≫ ambientParameter X.hom Y.hom) a
            (Graph.cutPoint (ambientParameter X.hom Y.hom) a G.inclusion
              (componentEndpointPoint X Y a E hE G w))]).homology n) :=
  (component_incidenceTor_graph_length X Y a E hE G w n).trans
    (Graph.polynomialTor_length (endpointAmbientSource X.hom Y.hom) X.hom
      (ambientParameter X.hom Y.hom) a G.inclusion (componentEndpointPoint X Y a E hE G w) n)

/-- Degree zero retains the actual principal endpoint quotient and its full length. -/
theorem component_incidenceTor_zero_length
    (w : (endpointComponentGenerator X a E hE).incidence G) :
    Module.length ((endpointComponentGenerator X a E hE).incidenceAmbientStalk G w)
      ((endpointComponentGenerator X a E hE).incidenceTor G w 0) =
      Module.length (G.scheme.presheaf.stalk
          (Graph.cutPoint (ambientParameter X.hom Y.hom) a G.inclusion
            (componentEndpointPoint X Y a E hE G w)))
        ((G.scheme.presheaf.stalk
          (Graph.cutPoint (ambientParameter X.hom Y.hom) a G.inclusion
            (componentEndpointPoint X Y a E hE G w))) ⧸
          Ideal.ofList [scalar (G.inclusion ≫ ambientParameter X.hom Y.hom) a
            (Graph.cutPoint (ambientParameter X.hom Y.hom) a G.inclusion
              (componentEndpointPoint X Y a E hE G w))]) :=
  (component_incidenceTor_graph_length X Y a E hE G w 0).trans
    (Graph.polynomialTor_zero_length (endpointAmbientSource X.hom Y.hom) X.hom
      (ambientParameter X.hom Y.hom) a G.inclusion (componentEndpointPoint X Y a E hE G w))

/-- A regular original endpoint scalar kills all positive original incidence Tor groups. -/
theorem component_incidenceTor_isZero_succ_of_scalar_regular
    (w : (endpointComponentGenerator X a E hE).incidence G)
    (hr : IsSMulRegular (G.scheme.presheaf.stalk
        (Graph.cutPoint (ambientParameter X.hom Y.hom) a G.inclusion
          (componentEndpointPoint X Y a E hE G w)))
      (scalar (G.inclusion ≫ ambientParameter X.hom Y.hom) a
        (Graph.cutPoint (ambientParameter X.hom Y.hom) a G.inclusion
          (componentEndpointPoint X Y a E hE G w)))) (n : ℕ) :
    IsZero ((endpointComponentGenerator X a E hE).incidenceTor G w (n + 1)) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply (Module.length_eq_zero_iff
    (R := (endpointComponentGenerator X a E hE).incidenceAmbientStalk G w)).mp
  rw [component_incidenceTor_graph_length]
  have := ModuleCat.isZero_iff_subsingleton.mp
    (Graph.polynomialTor_isZero_succ_of_scalar_regular (endpointAmbientSource X.hom Y.hom)
      X.hom (ambientParameter X.hom Y.hom) a G.inclusion
      (componentEndpointPoint X Y a E hE G w) hr n)
  exact Module.length_eq_zero

/-- Every actual right correspondence support dominates the parameter line.
Its finite projection reaches an entire relative-source component, and the
flat parameter projection takes that component's generic point to the generic point. -/
instance rightSupport_parameter_dominant :
    IsDominant (G.inclusion ≫ ambientParameter X.hom Y.hom) := by
  have hc : genericPoint G.scheme ∈ genericPoints G.scheme := by
    change closure ({genericPoint G.scheme} : Set G.scheme) ∈ irreducibleComponents G.scheme
    rw [(genericPoint_spec G.scheme).def, irreducibleComponents_eq_singleton]
    exact Set.mem_singleton _
  have hp := G.projection_mem_genericPoints (genericPoint G.scheme) hc
  have hq := mem_genericPoints_of_generalizing
    (pullback.snd X.hom (FiniteFlatCurveFamily.line k).hom)
    (Flat.generalizingMap _) (G.projection (genericPoint G.scheme)) hp
  change (G.inclusion ≫ ambientParameter X.hom Y.hom) (genericPoint G.scheme) ∈
    genericPoints (Spec (.of (Polynomial k))) at hq
  have hcl : closure
      ({(G.inclusion ≫ ambientParameter X.hom Y.hom) (genericPoint G.scheme)} :
        Set (Spec (.of (Polynomial k)))) = Set.univ := by
    simpa only [genericPoints, Set.mem_ofPred_eq, irreducibleComponents_eq_singleton,
      Set.mem_singleton_iff] using hq
  constructor
  rw [DenseRange, dense_iff_closure_eq, ← Set.univ_subset_iff, ← hcl]
  apply closure_mono
  rintro t (rfl : t = (G.inclusion ≫ ambientParameter X.hom Y.hom) (genericPoint G.scheme))
  exact ⟨genericPoint G.scheme, rfl⟩

/-- The literal original endpoint scalar is regular on every right support stalk.
No flatness over the relative source product is required. -/
theorem rightSupport_endpointScalar_regular (c : G.scheme) :
    IsSMulRegular (G.scheme.presheaf.stalk c)
      (scalar (G.inclusion ≫ ambientParameter X.hom Y.hom) a c) :=
  dominant_integral_affineScalar_isSMulRegular _ (Polynomial.X - Polynomial.C a)
    (Polynomial.X_sub_C_ne_zero a) c

/-- All positive original four-factor incidence Tor groups vanish for every
relative endpoint component, with no separate scalar-regularity premise. -/
theorem component_incidenceTor_isZero_succ
    (w : (endpointComponentGenerator X a E hE).incidence G) (n : ℕ) :
    IsZero ((endpointComponentGenerator X a E hE).incidenceTor G w (n + 1)) :=
  component_incidenceTor_isZero_succ_of_scalar_regular X Y a E hE G w
    (rightSupport_endpointScalar_regular X Y a G _) n

end Motivic.RelativeEndpointDiagram
