/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Incidence.TorCycle

/-!
# Consumers of actual diagonal-Tor incidence correspondences

These tests take genuine smooth-site generators over an arbitrary field.
They use actual categorical Tor coefficients, verify their finite local
lengths, recover actual finite pushforward through the faithful forgetful
map, and check signed biadditive extension on finite correspondence cycles.
No extra support or dominance hypothesis is supplied. The change-of-ambient
comparison with traditional triple-product Tor is a separate obligation.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme (IntegralCycle SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Motivic

universe u

namespace MotivicTest.TorIncidenceCycle

variable (k : Type u) [Field k]
  {X Y Z : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)

/-- Every degree of actual generic incidence Tor has finite local module length. -/
theorem actual_tor_lengths_finite (x : genericPoints (A.incidence B)) (n : ℕ) :
    Module.length (A.incidenceAmbientStalk B x.val) (A.incidenceTor B x.val n) ≠ ⊤ :=
  A.incidenceTor_length_ne_top (S := Spec (.of k)) B x n

/-- Actual Tor coefficients give an admissible correspondence without extra support witnesses. -/
noncomputable def actualTorCorrespondence : FiniteCorrespondence X.hom Z.hom :=
  A.incidenceTorCorrespondence k B

/-- The candidate operation has the literal four-factor diagonal-Tor-cycle pushforward. -/
theorem actual_pairing_is_tor_pushforward :
    FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Z.hom)
      (FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := Z) A.cycle B.cycle) =
      IntegralCycle.finitePushforward (A.incidenceMap B)
        (IntegralCycle.ofGenericCoefficients (A.incidence B)
          (A.incidenceTorCoefficient (S := Spec (.of k)) B)) := by
  rw [FiniteCorrespondence.incidenceTorPairing_cycle]
  exact A.toIntegralCycle_incidenceTorCorrespondence k B

/-- Signed integer multiplicities from both finite cycles are preserved literally. -/
theorem signed_basis_coefficients (m n : ℤ) :
    FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := Z)
      (Finsupp.single A m) (Finsupp.single B n) =
      (m * n) • A.incidenceTorCorrespondence k B :=
  FiniteCorrespondence.incidenceTorPairing_single k A B m n

/-- A signed combination of distinct or coincident actual generators distributes in both inputs. -/
theorem signed_generator_combination
    (A' : FiniteCorrespondenceGenerator X.hom Y.hom)
    (B' : FiniteCorrespondenceGenerator Y.hom Z.hom) :
    FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := Z)
      (A.cycle - A'.cycle) (B.cycle + B'.cycle) =
      (A.incidenceTorCorrespondence k B + A.incidenceTorCorrespondence k B') -
        (A'.incidenceTorCorrespondence k B + A'.incidenceTorCorrespondence k B') := by
  simp only [map_sub, AddMonoidHom.sub_apply, map_add,
    FiniteCorrespondence.incidenceTorPairing_cycle]
  exact sub_add_sub_comm _ _ _ _

end MotivicTest.TorIncidenceCycle
