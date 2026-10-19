/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.StalkLength
public import Motivic.Aglib.AlgebraicGeometry.Cycles.FundamentalStalk

/-!
# Finite-map Euler and actual generic-stalk consumers

These use literal scheme stalk restriction, its actual residue-field degree,
and the nonreduced generic multiplicity. Closed-immersion and isomorphism
consumers check the degree-one specialization. No global sheaf projection
formula or intersection associativity is assumed or asserted.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry _root_.HomologicalComplex.ModuleLengthEuler

universe u v

namespace Motivic.MotivicTest.FiniteStalkEuler
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (x : X)

/-- All actual finite-map stalk modules satisfy the residue-degree formula. -/
theorem actual_stalk_length (M : ModuleCat.{v} (X.presheaf.stalk x)) :
    Module.length (Y.presheaf.stalk (f x))
        ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj M) =
      Module.length (X.presheaf.stalk x) M * (f.residueDegree x : ℕ∞) :=
  length_finite_stalk_restrictScalars f x M

/-- The actual full generic structure stalk has the cycle's degree-weighted multiplicity. -/
theorem actual_generic_length [IsLocallyNoetherian X] (z : genericPoints X) :
    Module.length (Y.presheaf.stalk (f z.val))
        ((ModuleCat.restrictScalars (f.stalkMap z.val).hom).obj
          (ModuleCat.of (X.presheaf.stalk z.val) (X.presheaf.stalk z.val))) =
      (genericMultiplicity z * f.residueDegree z.val : ℕ) := by
  rw [length_finite_stalk_restrictScalars f z.val, ← genericMultiplicity_eq_length z]
  simp

/-- The generic coefficient formula never converts an infinite length to zero. -/
theorem actual_generic_length_finite [IsLocallyNoetherian X] (z : genericPoints X) :
    Module.length (Y.presheaf.stalk (f z.val))
        ((ModuleCat.restrictScalars (f.stalkMap z.val).hom).obj
          (ModuleCat.of (X.presheaf.stalk z.val) (X.presheaf.stalk z.val))) ≠ ⊤ := by
  rw [actual_generic_length]
  exact ENat.natCast_ne_top _

/-- A closed immersion has degree one, so actual stalk restriction preserves length. -/
theorem closed_immersion_length [IsClosedImmersion f]
    (M : ModuleCat.{v} (X.presheaf.stalk x)) :
    Module.length (Y.presheaf.stalk (f x))
        ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj M) =
      Module.length (X.presheaf.stalk x) M := by
  rw [length_finite_stalk_restrictScalars, residueDegree_of_surjectiveOnStalks]
  simp

/-- Any signs, including chain and cochain Euler signs, use the same actual residue degree. -/
theorem signed_actual_stalk_sum (M : ℤ → ModuleCat.{v} (X.presheaf.stalk x))
    (hM : FiniteLengthSupport M) :
    signedLengthSum
        (fun n => (ModuleCat.restrictScalars (f.stalkMap x).hom).obj (M n))
        (fun n => (n.negOnePow : ℤ))
        (finiteLengthSupport_finite_stalk_restrictScalars f x M hM) =
      signedLengthSum M (fun n => (n.negOnePow : ℤ)) hM * (f.residueDegree x : ℤ) :=
  signedLengthSum_finite_stalk_restrictScalars f x M _ hM

/-- An actual scheme isomorphism preserves all finite signed stalk Euler sums. -/
theorem iso_signed_stalk_sum [IsIso f] (M : ℕ → ModuleCat.{v} (X.presheaf.stalk x))
    (hM : FiniteLengthSupport M) :
    signedLengthSum
        (fun n => (ModuleCat.restrictScalars (f.stalkMap x).hom).obj (M n))
        (fun n => (-1 : ℤ) ^ n)
        (finiteLengthSupport_finite_stalk_restrictScalars f x M hM) =
      signedLengthSum M (fun n => (-1 : ℤ) ^ n) hM := by
  rw [signedLengthSum_finite_stalk_restrictScalars, residueDegree_of_isIso, Nat.cast_one, mul_one]

end Motivic.MotivicTest.FiniteStalkEuler
