/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.GlobalIncidenceAmbientTorComparison
public import Motivic.AlgebraicGeometry.Correspondences.TorIncidenceCycle

/-!
# Original global ambient-comparison consumers

The first consumer has no smoothness, affinity, perfectness, separability,
or finite-length assumptions. The smooth-site consumers derive the actual
finite-length and finite-degree evidence at generic incidence points, then
identify the existing finite-image assembly with the standard pulled-support
Tor formula. No associativity or category construction is asserted.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic.MotivicTest.GlobalIncidenceAmbientTorComparison

open Intersection _root_.Motivic.GlobalIncidenceAmbientTorComparison

variable (k : Type u) [Field k]

/-- Original global schemes and original support ideals, in every Tor degree. -/
theorem originalGlobalLength {X Y Z : Scheme.{u}}
    {f : X ⟶ Spec (.of k)} {g : Y ⟶ Spec (.of k)} {h : Z ⟶ Spec (.of k)}
    (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
    (w : F.incidence G) (n : ℕ) :
    Module.length (F.incidenceAmbientStalk G w) (F.incidenceTor G w n) =
      Module.length (ambientStalk (rightPulledInclusion G) (toRightPulled F G w))
        (pulledStalkTor F G w n) :=
  incidenceTor_length_eq_pulled k F G w n

variable {X Y Z : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)

/-- Smooth-site geometry proves finite length and bounded degree support for
original triple-product Tor at every actual generic incidence point. -/
theorem originalPulledFiniteLengthSupport (w : genericPoints (F.incidence G)) :
    LengthEuler.FiniteLengthSupport (pulledStalkTor F G w.val) :=
  (incidenceTor_finiteLengthSupport_iff_pulled k F G w.val).mp
    (F.incidenceTor_finiteLengthSupport (S := Spec (.of k)) G w.val w.property)

/-- The standard triple-product Tor Euler coefficient uses the original
pulled ideal subschemes and the proved finite-length support. -/
def originalPulledCoefficient (w : genericPoints (F.incidence G)) : ℤ :=
  LengthEuler.signedLengthSum (pulledStalkTor F G w.val) (fun n ↦ (-1 : ℤ) ^ n)
    (originalPulledFiniteLengthSupport k F G w)

/-- The actual generic diagonal-incidence coefficient agrees with every higher
Tor contribution in the original triple-product ambient intersection. -/
theorem originalCoefficientComparison (w : genericPoints (F.incidence G)) :
    F.incidenceTorCoefficient (S := Spec (.of k)) G w = originalPulledCoefficient k F G w :=
  incidenceTor_signedLengthSum_eq_pulled k F G w.val (fun n ↦ (-1 : ℤ) ^ n)
    (F.incidenceTor_finiteLengthSupport (S := Spec (.of k)) G w.val w.property)

/-- The existing generator composition has exactly the original triple-product
pulled-support Tor formula after its actual finite pushforward. All image
collisions and original residue-field degrees remain in that pushforward. -/
theorem originalAmbientFinitePushforward :
    FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Z.hom)
      (F.incidenceTorCorrespondence k G) =
      IntegralCycle.finitePushforward (F.incidenceMap G)
        (IntegralCycle.ofGenericCoefficients (F.incidence G)
          (originalPulledCoefficient k F G)) := by
  rw [F.toIntegralCycle_incidenceTorCorrespondence k G]
  congr 2
  funext w
  exact originalCoefficientComparison k F G w

end Motivic.MotivicTest.GlobalIncidenceAmbientTorComparison
