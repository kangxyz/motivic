/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.IncidenceTorAssociativity

/-!
# Actual arbitrary-field consumers of incidence Tor associativity

These consumers use the unchanged actual incidence Tor pairing. They cover
arbitrary signed cycles, all integer basis multiplicities, negative combinations,
zero inputs, and the faithful integral-cycle representation. No effectiveness,
connectedness, integrality, perfectness, or comparison hypothesis is supplied.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Motivic

universe u

namespace MotivicTest.IncidenceTorAssociativity

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}

/-- Arbitrary signed finite correspondence cycles associate over the given field. -/
theorem actualSignedCycleAssociativity
    (α : FiniteCorrespondence X.hom Y.hom)
    (β : FiniteCorrespondence Y.hom Z.hom)
    (γ : FiniteCorrespondence Z.hom W.hom) :
    FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Z) (Z := W)
        (FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := Z) α β) γ =
      FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := W)
        α (FiniteCorrespondence.incidenceTorPairing k (X := Y) (Y := Z) (Z := W) β γ) :=
  FiniteCorrespondence.incidenceTorPairing_assoc k
    (X := X) (Y := Y) (Z := Z) (W := W) α β γ

/-- Generator associativity consumes both literal bracket comparisons internally. -/
theorem actualGeneratorAssociativity
    (F : FiniteCorrespondenceGenerator X.hom Y.hom)
    (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
    (H : FiniteCorrespondenceGenerator Z.hom W.hom) :
    FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Z) (Z := W)
        (FiniteCorrespondence.incidenceTorPairing k
          (X := X) (Y := Y) (Z := Z) F.cycle G.cycle) H.cycle =
      FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := W)
        F.cycle (FiniteCorrespondence.incidenceTorPairing k
          (X := Y) (Y := Z) (Z := W) G.cycle H.cycle) :=
  FiniteCorrespondence.incidenceTorPairing_assoc_cycle k
    (X := X) (Y := Y) (Z := Z) (W := W) F G H

/-- Each of the three basis multiplicities ranges over all integers, including zero. -/
theorem actualIntegerBasisAssociativity
    (F : FiniteCorrespondenceGenerator X.hom Y.hom)
    (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
    (H : FiniteCorrespondenceGenerator Z.hom W.hom) (m n p : ℤ) :
    FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Z) (Z := W)
        (FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := Z)
          (Finsupp.single F m) (Finsupp.single G n))
        (Finsupp.single H p) =
      FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := W)
        (Finsupp.single F m)
        (FiniteCorrespondence.incidenceTorPairing k (X := Y) (Y := Z) (Z := W)
          (Finsupp.single G n) (Finsupp.single H p)) :=
  FiniteCorrespondence.incidenceTorPairing_assoc k
    (X := X) (Y := Y) (Z := Z) (W := W) _ _ _

/-- Negative and subtractive inputs are ordinary finite correspondence cycles. -/
theorem actualNegativeCombinationAssociativity
    (α α' : FiniteCorrespondence X.hom Y.hom)
    (β : FiniteCorrespondence Y.hom Z.hom)
    (γ : FiniteCorrespondence Z.hom W.hom) :
    FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Z) (Z := W)
        (FiniteCorrespondence.incidenceTorPairing k
          (X := X) (Y := Y) (Z := Z) (α - α') (-β)) ((-3 : ℤ) • γ) =
      FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := W)
        (α - α') (FiniteCorrespondence.incidenceTorPairing k
          (X := Y) (Y := Z) (Z := W) (-β) ((-3 : ℤ) • γ)) :=
  FiniteCorrespondence.incidenceTorPairing_assoc k
    (X := X) (Y := Y) (Z := Z) (W := W) _ _ _

/-- A zero middle cycle is included in the same actual associativity theorem. -/
theorem actualZeroMiddleAssociativity
    (α : FiniteCorrespondence X.hom Y.hom)
    (γ : FiniteCorrespondence Z.hom W.hom) :
    FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Z) (Z := W)
        (FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := Z) α 0) γ =
      FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := W)
        α (FiniteCorrespondence.incidenceTorPairing k (X := Y) (Y := Z) (Z := W) 0 γ) :=
  FiniteCorrespondence.incidenceTorPairing_assoc k
    (X := X) (Y := Y) (Z := Z) (W := W) α 0 γ

/-- The actual two brackets also agree as integral cycles on the outer product. -/
theorem actualIntegralCycleAssociativity
    (α : FiniteCorrespondence X.hom Y.hom)
    (β : FiniteCorrespondence Y.hom Z.hom)
    (γ : FiniteCorrespondence Z.hom W.hom) :
    FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := W.hom)
        (FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Z) (Z := W)
          (FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := Z) α β) γ) =
      FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := W.hom)
        (FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := W)
          α (FiniteCorrespondence.incidenceTorPairing k (X := Y) (Y := Z) (Z := W) β γ)) :=
  congrArg (FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := W.hom))
    (FiniteCorrespondence.incidenceTorPairing_assoc k
    (X := X) (Y := Y) (Z := Z) (W := W) α β γ)

end MotivicTest.IncidenceTorAssociativity
