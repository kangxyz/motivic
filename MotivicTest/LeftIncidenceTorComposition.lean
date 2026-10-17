/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.LeftIncidenceTorComposition

/-!
# Actual arbitrary-field consumers of the left Tor composition comparison

The consumers use the actual Tor pairing, the actual canonical triple Tor
correspondence, and its literal finite-pushforward cycle. Their only inputs
are the field, four smooth-site objects, and three correspondence generators.
No regular list, coefficient replacement, support injection, or comparison
equality is supplied. The right bracket and associativity remain separate.

These source-only consumers require their own strict compilation check.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

namespace MotivicTest.LeftIncidenceTorComposition

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

/-- An actual left generator bracket is the actual canonical triple correspondence. -/
theorem actualLeftTorBracket :
    FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Z) (Z := W)
      (F.incidenceTorCorrespondence k G) H.cycle = F.tripleTorCorrespondence k G H :=
  F.incidenceTorPairing_left_eq_tripleTorCorrespondence k G H

/-- The two literally nested pairings consume the three original generator cycles. -/
theorem actualNestedLeftTorPairing :
    FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Z) (Z := W)
      (FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := Z)
        F.cycle G.cycle) H.cycle = F.tripleTorCorrespondence k G H :=
  F.incidenceTorPairing_left_cycle_eq_tripleTorCorrespondence k G H

/-- Forgetting the bracket gives the genuine canonical triple finite-pushforward cycle. -/
theorem actualLeftTorBracketIntegralCycle :
    FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := W.hom)
        (FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Z) (Z := W)
          (F.incidenceTorCorrespondence k G) H.cycle) =
      IntegralCycle.finitePushforward (F.tripleIncidenceMap G H)
        (F.tripleIncidenceTorCycle k G H) :=
  F.toIntegralCycle_incidenceTorPairing_left k G H

end MotivicTest.LeftIncidenceTorComposition
