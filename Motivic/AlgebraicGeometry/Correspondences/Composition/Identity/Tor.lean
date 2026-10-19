/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Identity.Cycle
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Identity.OpenGraph

/-!
# Actual Tor comparison for every smooth diagonal component

The genuine diagonal component projections are open immersions. Therefore
the actual incidence Tor has no positive terms, and the actual Euler
coefficient equals full local incidence multiplicity. These conclusions hold
for every component of an arbitrary smooth object, without any global
integrality or nonemptiness assumption. Finite-sum unit assembly remains a
separate geometric cycle calculation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] {X Y : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)

/-- Every right diagonal component has zero positive actual incidence Tor. -/
theorem isZero_incidenceTor_succ_componentIdentity_right
    (C : Set Y.left) (hC : C ∈ irreducibleComponents Y.left)
    (w : A.incidence (componentIdentityGenerator (X := Y.left) Y.hom C hC)) (n : ℕ) :
    IsZero (A.incidenceTor (componentIdentityGenerator (X := Y.left) Y.hom C hC) w (n + 1)) :=
  A.isZero_incidenceTor_succ_of_isOpenImmersion_projection
    (componentIdentityGenerator (X := Y.left) Y.hom C hC) w n

/-- Every left diagonal component has zero positive actual incidence Tor. -/
theorem isZero_incidenceTor_succ_componentIdentity_left
    (C : Set X.left) (hC : C ∈ irreducibleComponents X.left)
    (w : (componentIdentityGenerator (X := X.left) X.hom C hC).incidence A) (n : ℕ) :
    IsZero ((componentIdentityGenerator (X := X.left) X.hom C hC).incidenceTor A w (n + 1)) :=
  isZero_incidenceTor_succ_of_isOpenImmersion_targetProjection
    (componentIdentityGenerator (X := X.left) X.hom C hC) A w n

/-- Actual right-component Tor coefficients are the full generic stalk multiplicities. -/
theorem incidenceTorCoefficient_componentIdentity_right
    (C : Set Y.left) (hC : C ∈ irreducibleComponents Y.left)
    (x : genericPoints (A.incidence (componentIdentityGenerator (X := Y.left) Y.hom C hC))) :
    A.incidenceTorCoefficient (S := Spec (.of k))
      (componentIdentityGenerator (X := Y.left) Y.hom C hC) x =
      (genericMultiplicity x : ℤ) :=
  A.incidenceTorCoefficient_eq_genericMultiplicity_of_isOpenImmersion_projection k
    (componentIdentityGenerator (X := Y.left) Y.hom C hC) x

/-- Actual left-component Tor coefficients are the full generic stalk multiplicities. -/
theorem incidenceTorCoefficient_componentIdentity_left
    (C : Set X.left) (hC : C ∈ irreducibleComponents X.left)
    (x : genericPoints ((componentIdentityGenerator (X := X.left) X.hom C hC).incidence A)) :
    incidenceTorCoefficient (S := Spec (.of k))
      (componentIdentityGenerator (X := X.left) X.hom C hC) A x =
      (genericMultiplicity x : ℤ) :=
  incidenceTorCoefficient_eq_genericMultiplicity_of_isOpenImmersion_targetProjection k
    (componentIdentityGenerator (X := X.left) X.hom C hC) A x

/-- The full right-component actual Tor correspondence equals genuine fundamental incidence. -/
theorem incidenceTorCorrespondence_componentIdentity_right
    (C : Set Y.left) (hC : C ∈ irreducibleComponents Y.left) :
    A.incidenceTorCorrespondence k (componentIdentityGenerator (X := Y.left) Y.hom C hC) =
      A.incidenceFundamentalCorrespondence k
        (componentIdentityGenerator (X := Y.left) Y.hom C hC) :=
  A.incidenceTorCorrespondence_eq_fundamental_of_isOpenImmersion_projection k
    (componentIdentityGenerator (X := Y.left) Y.hom C hC)

/-- The full left-component actual Tor correspondence equals genuine fundamental incidence. -/
theorem incidenceTorCorrespondence_componentIdentity_left
    (C : Set X.left) (hC : C ∈ irreducibleComponents X.left) :
    (componentIdentityGenerator (X := X.left) X.hom C hC).incidenceTorCorrespondence k A =
      incidenceFundamentalCorrespondence k
        (componentIdentityGenerator (X := X.left) X.hom C hC) A :=
  incidenceTorCorrespondence_eq_fundamental_of_isOpenImmersion_targetProjection k
    (componentIdentityGenerator (X := X.left) X.hom C hC) A

/-- Every nonempty generic right-component incidence has exact coefficient one. -/
theorem incidenceTorCoefficient_componentIdentity_right_eq_one
    (C : Set Y.left) (hC : C ∈ irreducibleComponents Y.left)
    (x : genericPoints (A.incidence (componentIdentityGenerator (X := Y.left) Y.hom C hC))) :
    A.incidenceTorCoefficient (S := Spec (.of k))
      (componentIdentityGenerator (X := Y.left) Y.hom C hC) x = 1 := by
  have : IsOpenImmersion
      (A.incidenceFst (componentIdentityGenerator (X := Y.left) Y.hom C hC)) :=
    inferInstanceAs (IsOpenImmersion (pullback.fst A.targetProjection
      (componentIdentityGenerator (X := Y.left) Y.hom C hC).projection))
  have : IsReduced (A.incidence (componentIdentityGenerator (X := Y.left) Y.hom C hC)) :=
    isReduced_of_isOpenImmersion
      (A.incidenceFst (componentIdentityGenerator (X := Y.left) Y.hom C hC))
  rw [A.incidenceTorCoefficient_componentIdentity_right k, genericMultiplicity_eq_one]
  rfl

/-- Every nonempty generic left-component incidence has exact coefficient one. -/
theorem incidenceTorCoefficient_componentIdentity_left_eq_one
    (C : Set X.left) (hC : C ∈ irreducibleComponents X.left)
    (x : genericPoints ((componentIdentityGenerator (X := X.left) X.hom C hC).incidence A)) :
    incidenceTorCoefficient (S := Spec (.of k))
      (componentIdentityGenerator (X := X.left) X.hom C hC) A x = 1 := by
  have : IsOpenImmersion
      ((componentIdentityGenerator (X := X.left) X.hom C hC).incidenceSnd A) :=
    inferInstanceAs (IsOpenImmersion (pullback.snd
      (componentIdentityGenerator (X := X.left) X.hom C hC).targetProjection A.projection))
  have : IsReduced ((componentIdentityGenerator (X := X.left) X.hom C hC).incidence A) :=
    isReduced_of_isOpenImmersion
      ((componentIdentityGenerator (X := X.left) X.hom C hC).incidenceSnd A)
  rw [A.incidenceTorCoefficient_componentIdentity_left k, genericMultiplicity_eq_one]
  rfl

end Motivic.FiniteCorrespondenceGenerator
