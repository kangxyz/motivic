/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.IncidenceTor
public import Motivic.AlgebraicGeometry.SmoothSiteNoetherian

/-!
# Actual incidence Tor consumers over arbitrary fields

For genuine finite-correspondence generators between smooth-site objects,
the actual stalk Tor coefficient needs no assumed regular-equation record,
finite-support record, coefficient regularity, or reduced incidence scheme.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.MotivicTest.IncidenceTor

variable (k : Type u) [Field k] {X Y Z : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)

/-- The coefficient is a genuine actual generic-incidence integer over any field. -/
noncomputable def actualCoefficient (w : genericPoints (A.incidence B)) : ℤ :=
  A.incidenceTorCoefficient (S := Spec (.of k)) B w

/-- Every categorical Tor correction has finite length with all geometric facts derived. -/
theorem actualTorLength (w : genericPoints (A.incidence B)) (n : ℕ) :
    Module.length (A.incidenceAmbientStalk B w.val) (A.incidenceTor B w.val n) ≠ ⊤ :=
  A.incidenceTor_length_ne_top (S := Spec (.of k)) B w n

/-- The actual support-product stalk is finite over the actual four-factor ambient stalk. -/
theorem actualCoefficientFinite (w : A.incidence B) :
    Module.Finite (A.incidenceAmbientStalk B w) (A.incidenceSupportStalkModule B w) :=
  inferInstance

/-- The scalar module really has the support-product stalk as its underlying type. -/
theorem actualSupportStalk (w : A.incidence B) :
    (A.incidenceSupportStalkModule B w : Type u) =
      (A.supportProduct B).presheaf.stalk (A.incidenceToSupportProduct B w) := rfl

/-- The coefficient sums actual Tor lengths with every finite higher correction retained. -/
theorem actualCoefficientFormula (w : genericPoints (A.incidence B)) :
    actualCoefficient k A B w =
      LengthEuler.signedLengthSum (A.incidenceTor B w.val) (fun n => (-1 : ℤ) ^ n)
        (A.incidenceTor_finiteLengthSupport (S := Spec (.of k)) B w.val w.property) := rfl

end Motivic.MotivicTest.IncidenceTor
