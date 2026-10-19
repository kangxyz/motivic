/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Exterior.Identity.TorCycle
public import Motivic.Aglib.AlgebraicGeometry.Simplex.ExteriorGeometry

/-! # Consumers of the actual exterior incidence Tor cycle -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open _root_.AlgebraicGeometry.Scheme.Cycles.BaseChange.ComponentDecomposition
open scoped BigOperators

universe u

namespace MotivicTest.ExteriorIdentityTorCycle
open _root_.AlgebraicGeometry.Scheme (IntegralCycle SmoothSite)

variable {k : Type u} [Field k] {X Y Z : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom]

local instance : IsNoetherian (A.exteriorIncidenceSupport B T) :=
  _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType (pullback.fst (A.incidenceSource B ≫
      X.hom) T.hom)

local instance (x : genericPoints (A.incidence B)) :
    IsNoetherian (componentExterior (A.incidenceSource B ≫ X.hom) T.hom x) :=
  _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType
    (componentExteriorInclusion (A.incidenceSource B ≫ X.hom) T.hom x)

example :
    IntegralCycle.ofGenericCoefficients
      ((A.exteriorIdentityGenerator T).incidence (B.exteriorIdentityGenerator T))
      ((A.exteriorIdentityGenerator T).incidenceTorCoefficient (S := Spec (.of k))
        (B.exteriorIdentityGenerator T)) =
    letI := IntegralCycle.genericPointFintype (A.incidence B)
    IntegralCycle.finitePushforward (A.exteriorIdentityIncidenceIso B T).hom
      (∑ x : genericPoints (A.incidence B),
        A.incidenceTorCoefficient (S := Spec (.of k)) B x •
          IntegralCycle.finitePushforward
            (componentExteriorInclusion (A.incidenceSource B ≫ X.hom) T.hom x)
            (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (componentExterior (A.incidenceSource
                B ≫ X.hom) T.hom x))) :=
  A.exteriorIncidenceTorCycle_eq_component_sum B T

end MotivicTest.ExteriorIdentityTorCycle
