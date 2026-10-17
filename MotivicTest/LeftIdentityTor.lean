/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.LeftIdentityTor

/-!
# Consumers of the genuine left-identity Tor law

These consumers retain the actual Tor objects, same ambient kernel list,
full zeroth-Tor intersection stalk length, canonical Euler coefficients,
and arbitrary signed cycles. Only the smooth source is integral so that its
identity is one generator. The smooth target can be disconnected.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingTheory.Sequence Motivic Motivic.FiniteCorrespondenceGenerator

universe u

namespace MotivicTest.LeftIdentityTor

variable (k : Type u) [Field k] {X Y : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  [IsIntegral ((𝟭 Scheme).obj X.left)]

/-- Geometry proves the same actual ambient kernel list regular on both actual modules. -/
theorem actual_common_list (w : (identityGenerator X.hom).incidence A) :
    ∃ s : List ((identityGenerator X.hom).incidenceAmbientStalk A w),
      RingHom.ker ((correspondenceTripleInclusion X.hom X.hom Y.hom).stalkMap
        ((identityGenerator X.hom).incidenceInclusion A w)).hom = Ideal.ofList s ∧
      IsRegular ((identityGenerator X.hom).incidenceAmbientStalk A w) s ∧
      IsWeaklyRegular ((identityGenerator X.hom).incidenceSupportStalkModule A w) s :=
  (identityGenerator X.hom).exists_incidence_regular_list_of_isIso_targetProjection A w

/-- Every positive actual incidence Tor vanishes, even away from generic points. -/
theorem identity_positive_tor (w : (identityGenerator X.hom).incidence A) (n : ℕ) :
    IsZero ((identityGenerator X.hom).incidenceTor A w (n + 1)) :=
  (identityGenerator X.hom).isZero_incidenceTor_succ_of_isIso_targetProjection A w n

/-- Zeroth actual categorical Tor has the full actual intersection stalk length. -/
theorem identity_tor_zero_length (w : (identityGenerator X.hom).incidence A) :
    Module.length ((identityGenerator X.hom).incidenceAmbientStalk A w)
        ((identityGenerator X.hom).incidenceTor A w 0) =
      Module.length (((identityGenerator X.hom).incidence A).presheaf.stalk w)
        (((identityGenerator X.hom).incidence A).presheaf.stalk w) :=
  Intersection.length_tor_zero_eq_stalk
    (correspondenceTripleInclusion X.hom X.hom Y.hom)
    ((identityGenerator X.hom).supportProductInclusion A)
    ((identityGenerator X.hom).incidenceInclusion A)
    ((identityGenerator X.hom).incidenceToSupportProduct A)
    ((identityGenerator X.hom).incidence_ambient_isPullback A) w

/-- The canonical full Euler coefficient is actually one on left identity incidence. -/
theorem identity_actual_coefficient
    (x : genericPoints ((identityGenerator X.hom).incidence A)) :
    (identityGenerator X.hom).incidenceTorCoefficient (S := Spec (.of k)) A x = 1 := by
  rw [incidenceTorCoefficient_eq_genericMultiplicity_of_isIso_targetProjection k]
  have hm := genericMultiplicity_mapGenericPoint A.leftIdentityIncidenceIso.hom x
  rw [genericMultiplicity_eq_one] at hm
  rw [← hm]
  rfl

/-- The genuine Tor incidence cycle with a single actual left identity is the original cycle. -/
theorem identity_actual_generator :
    (identityGenerator X.hom).incidenceTorCorrespondence k A = A.cycle :=
  A.incidenceTorCorrespondence_identity_left k

/-- Signed basis coefficients remain unchanged under the actual left identity pairing. -/
theorem signed_identity_basis (n : ℤ) :
    FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := X) (Z := Y)
      (identityGenerator X.hom).cycle (Finsupp.single A n) = Finsupp.single A n :=
  FiniteCorrespondence.incidenceTorPairing_identity_left k _

/-- The actual single identity graph is a left unit for every signed correspondence cycle. -/
theorem arbitrary_signed_left_unit (α : FiniteCorrespondence X.hom Y.hom) :
    FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := X) (Z := Y)
      (identityGenerator X.hom).cycle α = α :=
  FiniteCorrespondence.incidenceTorPairing_identity_left k α

end MotivicTest.LeftIdentityTor
