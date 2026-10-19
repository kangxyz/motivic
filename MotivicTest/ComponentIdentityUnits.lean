/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Identity.Units

/-!
# Consumers of genuine full componentwise identity laws

The source and target remain arbitrary smooth objects. The actual signed
Tor incidence pairing is tested against the complete geometric diagonal.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Motivic

universe u

namespace MotivicTest.ComponentIdentityUnits
open _root_.AlgebraicGeometry.Scheme (SmoothSite)

variable (k : Type u) [Field k] {X Y : SmoothSite (Spec (.of k))}

/-- Arbitrary signed cycles have the actual full diagonal as a right unit. -/
theorem arbitrary_signed_right_unit (α : FiniteCorrespondence X.hom Y.hom) :
    FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := Y)
      α (componentIdentityCycle (X := Y.left) Y.hom) = α :=
  FiniteCorrespondence.incidenceTorPairing_componentIdentity_right k α

/-- Arbitrary signed cycles have the actual full diagonal as a left unit. -/
theorem arbitrary_signed_left_unit (α : FiniteCorrespondence X.hom Y.hom) :
    FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := X) (Z := Y)
      (componentIdentityCycle (X := X.left) X.hom) α = α :=
  FiniteCorrespondence.incidenceTorPairing_componentIdentity_left k α

/-- The actual full identity on an empty smooth object is the empty cycle. -/
theorem empty_identity [IsEmpty X.left] :
    componentIdentityCycle (X := X.left) X.hom = 0 :=
  componentIdentityCycle_eq_zero_of_isEmpty (X := X.left) X.hom

/-- On an integral object the new identity is the certified original generator. -/
theorem integral_identity [IsIntegral X.left] :
    componentIdentityCycle (X := X.left) X.hom = (identityGenerator (X := X.left) X.hom).cycle :=
  componentIdentityCycle_eq_identityGenerator_cycle (X := X.left) X.hom

end MotivicTest.ComponentIdentityUnits
