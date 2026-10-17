/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.ComponentIdentityTor

/-!
# Consumers of genuine component diagonal Tor comparisons

These consumers use every smooth component without a global integrality
assumption, checking actual positive Tor and the full multiplicity comparison.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

namespace MotivicTest.ComponentIdentityTor

variable (k : Type u) [Field k] {X Y : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)

/-- The whole smooth diagonal has coefficient one on every actual component. -/
theorem identity_coefficient_one (C : Set X.left) (hC : C ∈ irreducibleComponents X.left) :
    componentIdentityCycle (X := X.left) X.hom
      (componentIdentityGenerator (X := X.left) X.hom C hC) = 1 :=
  componentIdentityCycle_coefficient (X := X.left) X.hom C hC

/-- Right-component actual positive Tor vanishes at every incidence point. -/
theorem right_component_positive_tor
    (C : Set Y.left) (hC : C ∈ irreducibleComponents Y.left)
    (w : A.incidence (componentIdentityGenerator (X := Y.left) Y.hom C hC)) (n : ℕ) :
    IsZero (A.incidenceTor (componentIdentityGenerator (X := Y.left) Y.hom C hC) w (n + 1)) :=
  A.isZero_incidenceTor_succ_componentIdentity_right k C hC w n

/-- Left-component actual positive Tor vanishes at every incidence point. -/
theorem left_component_positive_tor
    (C : Set X.left) (hC : C ∈ irreducibleComponents X.left)
    (w : (componentIdentityGenerator (X := X.left) X.hom C hC).incidence A) (n : ℕ) :
    IsZero ((componentIdentityGenerator (X := X.left) X.hom C hC).incidenceTor A w (n + 1)) :=
  A.isZero_incidenceTor_succ_componentIdentity_left k C hC w n

/-- Both signs are retained when assembling the right-component Tor comparison. -/
theorem signed_right_component (C : Set Y.left) (hC : C ∈ irreducibleComponents Y.left)
    (m n : ℤ) :
    FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := Y)
      (Finsupp.single A m)
      (Finsupp.single (componentIdentityGenerator (X := Y.left) Y.hom C hC) n) =
        (m * n) • A.incidenceFundamentalCorrespondence k
          (componentIdentityGenerator (X := Y.left) Y.hom C hC) := by
  rw [FiniteCorrespondence.incidenceTorPairing_single,
    A.incidenceTorCorrespondence_componentIdentity_right k]

/-- Faithful forgetting retains the full actual fundamental pushforward on the left. -/
theorem left_component_full_pushforward
    (C : Set X.left) (hC : C ∈ irreducibleComponents X.left) :
    FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Y.hom)
      ((componentIdentityGenerator (X := X.left) X.hom C hC).incidenceTorCorrespondence k A) =
      IntegralCycle.finitePushforward
        ((componentIdentityGenerator (X := X.left) X.hom C hC).incidenceMap A)
        (fundamentalCycle ((componentIdentityGenerator (X := X.left) X.hom C hC).incidence A)) := by
  rw [A.incidenceTorCorrespondence_componentIdentity_left k]
  exact FiniteCorrespondenceGenerator.toIntegralCycle_incidenceFundamentalCorrespondence k
    (componentIdentityGenerator (X := X.left) X.hom C hC) A

/-- Actual generic component incidence retains exact multiplicity one. -/
theorem right_component_coefficient_one
    (C : Set Y.left) (hC : C ∈ irreducibleComponents Y.left)
    (x : genericPoints (A.incidence (componentIdentityGenerator (X := Y.left) Y.hom C hC))) :
    A.incidenceTorCoefficient (S := Spec (.of k))
      (componentIdentityGenerator (X := Y.left) Y.hom C hC) x = 1 :=
  A.incidenceTorCoefficient_componentIdentity_right_eq_one k C hC x

end MotivicTest.ComponentIdentityTor
