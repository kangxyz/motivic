/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Incidence.RightComposition

/-!
# Actual arbitrary-field consumers of the right Tor composition comparison

The consumers use the actual Tor pairing, the same canonical triple Tor
correspondence, and its literal finite-pushforward cycle. Their only inputs
are the field, four smooth-site objects, and three correspondence generators.
No regular list, coefficient replacement, support injection, flatness of F,
or comparison equality is supplied. General associativity remains separate.

These source-only consumers require their own strict compilation check.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.AlgebraicGeometry.Scheme (IntegralCycle SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

namespace MotivicTest.RightIncidenceTorComposition

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

/-- An actual right generator bracket is the same canonical triple correspondence. -/
theorem actualRightTorBracket :
    FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := W)
      F.cycle (G.incidenceTorCorrespondence (X := Y) (Y := Z) (Z := W) k H) =
        F.tripleTorCorrespondence k G H :=
  F.incidenceTorPairing_right_eq_tripleTorCorrespondence k G H

/-- The two literally nested pairings consume the three original generator cycles. -/
theorem actualNestedRightTorPairing :
    FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := W)
      F.cycle (FiniteCorrespondence.incidenceTorPairing k (X := Y) (Y := Z) (Z := W)
        G.cycle H.cycle) = F.tripleTorCorrespondence k G H :=
  F.incidenceTorPairing_right_cycle_eq_tripleTorCorrespondence k G H

/-- Forgetting the bracket gives the genuine canonical triple finite-pushforward cycle. -/
theorem actualRightTorBracketIntegralCycle :
    FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := W.hom)
        (FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := W)
          F.cycle (G.incidenceTorCorrespondence (X := Y) (Y := Z) (Z := W) k H)) =
      IntegralCycle.finitePushforward (F.tripleIncidenceMap G H)
        (F.tripleIncidenceTorCycle k G H) :=
  F.toIntegralCycle_incidenceTorPairing_right k G H

end MotivicTest.RightIncidenceTorComposition
