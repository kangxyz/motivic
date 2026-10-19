/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.Endpoints

public import Motivic.AlgebraicGeometry.Correspondences.Endpoints.Relative.IncidenceTor
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Incidence.TransverseCycle

/-!
# Full fundamental incidence cycles for relative endpoint components

The proved positive-Tor vanishing reduces the original finite Tor Euler sum to
its zeroth term. The existing actual Cartesian intersection-stalk isomorphism
identifies that term with the full generic incidence length. Hence the actual
component endpoint composition retains the whole possibly nonreduced incidence
fundamental cycle, with unchanged finite-image degrees and collisions.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram
open _root_.AlgebraicGeometry.Scheme.SmoothSite

variable {k : Type u} [Field k] (X Y : SmoothSite (Spec (.of k)))
  (a : k) (E : Set X.left) (hE : E ∈ irreducibleComponents X.left)
  (G : _root_.Motivic.FiniteCorrespondenceGenerator (relativeLineHom X.hom) Y.hom)

local instance : IsNoetherian ((endpointComponentGenerator X a E hE).incidence G) :=
  _root_.Motivic.FiniteCorrespondenceGenerator.isNoetherian_smoothIncidence k
    (X := X) (Y := relativeLineSite X) (Z := Y) (endpointComponentGenerator X a E hE) G

/-- The original Tor Euler coefficient is the full generic incidence multiplicity. -/
theorem component_incidenceTorCoefficient_eq_genericMultiplicity
    (x : genericPoints ((endpointComponentGenerator X a E hE).incidence G)) :
    (endpointComponentGenerator X a E hE).incidenceTorCoefficient (S := Spec (.of k)) G x =
      (genericMultiplicity x : ℤ) := by
  let F := endpointComponentGenerator X a E hE
  unfold _root_.Motivic.FiniteCorrespondenceGenerator.incidenceTorCoefficient
  rw [_root_.HomologicalComplex.ModuleLengthEuler.signedLengthSum_eq_sum _ _ _ {0}]
  · simp only [Finset.sum_singleton, pow_zero, one_mul,
      _root_.HomologicalComplex.ModuleLengthEuler.integerLength]
    have he := Intersection.length_tor_zero_eq_stalk
      (correspondenceTripleInclusion X.hom (relativeLineHom X.hom) Y.hom)
      (F.supportProductInclusion G) (F.incidenceInclusion G) (F.incidenceToSupportProduct G)
      (F.incidence_ambient_isPullback G) x.val
    exact congrArg (fun l : ℕ∞ => (l.toNat : ℤ)) he
  · intro n hn
    by_contra hn0
    have hn0 : n ≠ 0 := by simpa using hn0
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have : Subsingleton (F.incidenceTor G x.val (m + 1)) :=
      ModuleCat.subsingleton_of_isZero (component_incidenceTor_isZero_succ X Y a E hE G x.val m)
    exact hn Module.length_eq_zero

/-- The actual endpoint component Tor correspondence equals its whole ordinary
incidence fundamental correspondence, without flatness of the right support. -/
theorem component_incidenceTorCorrespondence_eq_fundamental :
    (endpointComponentGenerator X a E hE).incidenceTorCorrespondence k
        (X := X) (Y := relativeLineSite X) (Z := Y) G =
      (endpointComponentGenerator X a E hE).incidenceFundamentalCorrespondence k
        (X := X) (Y := relativeLineSite X) (Z := Y) G := by
  unfold _root_.Motivic.FiniteCorrespondenceGenerator.incidenceTorCorrespondence
    _root_.Motivic.FiniteCorrespondenceGenerator.incidenceFundamentalCorrespondence
  apply congrArg ((endpointComponentGenerator X a E hE).incidenceCycleAssembly k
    (X := X) (Y := relativeLineSite X) (Z := Y) G)
  funext x
  exact component_incidenceTorCoefficient_eq_genericMultiplicity X Y a E hE G x

/-- Forgetting the endpoint component composition gives finite pushforward of
the full original incidence fundamental cycle, retaining all local lengths. -/
theorem component_toIntegralCycle_incidenceTorCorrespondence :
    _root_.Motivic.FiniteCorrespondence.toIntegralCycle
      ((endpointComponentGenerator X a E hE).incidenceTorCorrespondence k
        (X := X) (Y := relativeLineSite X) (Z := Y) G) =
      IntegralCycle.finitePushforward ((endpointComponentGenerator X a E hE).incidenceMap G)
        (fundamentalCycle ((endpointComponentGenerator X a E hE).incidence G)) := by
  rw [component_incidenceTorCorrespondence_eq_fundamental]
  exact (endpointComponentGenerator X a E hE).toIntegralCycle_incidenceFundamentalCorrespondence k
    (X := X) (Y := relativeLineSite X) (Z := Y) G

end AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram
