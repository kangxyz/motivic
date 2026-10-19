/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.LengthEuler.FiniteAlgebra
public import Motivic.Aglib.Algebra.Homology.LengthEuler.Single
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Consumers of the finite-algebra homology Euler formula

Single complexes test the actual exact-restriction homology comparison. The
two-branch algebra over a field is genuinely nonlocal, and its structure map
is not surjective. Its degree-one complex has fiber Euler characteristic -2.
-/

@[expose] public section

noncomputable section

open CategoryTheory HomologicalComplex

universe u

namespace Motivic.MotivicTest.LengthEulerFiniteAlgebra

open _root_.HomologicalComplex.ModuleLengthEuler

variable (R S : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [CommRing S] [Algebra R S] [Module.Finite R S]

/-- For a single complex in any degree, the derived all-point fiber sum
computes the sign times the length of the actual restricted module. -/
theorem singleFiberEuler (M : ModuleCat.{u} S) (hM : Module.length S M ≠ ⊤) (j : ℕ) :
    finiteAlgebraFiberEuler R S ((single (ModuleCat S) (ComplexShape.down ℕ) j).obj M)
        (fun i => (-1) ^ i) (finiteHomology_single _ j M hM) =
      (-1 : ℤ) ^ j * integerLength ((ModuleCat.restrictScalars (algebraMap R S)).obj M)
        (finiteAlgebra_restrict_length_ne_top R S M hM) := by
  let C := (single (ModuleCat S) (ComplexShape.down ℕ) j).obj M
  have hC : FiniteHomology C := finiteHomology_single _ j M hM
  let N := (ModuleCat.restrictScalars (algebraMap R S)).obj M
  have hN : Module.length R N ≠ ⊤ := finiteAlgebra_restrict_length_ne_top R S M hM
  let e : finiteAlgebraRestrictedComplex R S C ≅
      (single (ModuleCat R) (ComplexShape.down ℕ) j).obj N :=
    (singleMapHomologicalComplex (ModuleCat.restrictScalars (algebraMap R S)) _ j).app M
  rw [← homologyEuler_finiteAlgebra_eq_fiberEuler R S C (fun i => (-1) ^ i) hC]
  rw [homologyEuler_eq_of_quasiIso e.hom (fun i => (-1) ^ i) _
    (finiteHomology_single _ j N hN)]
  exact homologyEuler_single _ j N (fun i => (-1) ^ i) hN

variable (k : Type u) [Field k]

/-- The two-branch regular module has actual finite length over its algebra. -/
theorem twoBranchFiniteLength : Module.length (k × k) (k × k) ≠ ⊤ := by
  have : IsArtinianRing (k × k) := IsArtinianRing.of_finite k (k × k)
  exact Module.length_ne_top

/-- Both maximal points above the single base-field point contribute,
with the correct alternating sign in every degree. -/
theorem twoBranchSingleEuler (j : ℕ) :
    finiteAlgebraFiberEuler k (k × k)
        ((single (ModuleCat (k × k)) (ComplexShape.down ℕ) j).obj
          (ModuleCat.of (k × k) (k × k)))
        (fun i => (-1) ^ i)
        (finiteHomology_single _ j _ (twoBranchFiniteLength k)) = (-1 : ℤ) ^ j * 2 := by
  rw [singleFiberEuler k (k × k) _ (twoBranchFiniteLength k) j]
  congr 1
  let e : (ModuleCat.restrictScalars (algebraMap k (k × k))).obj
      (ModuleCat.of (k × k) (k × k)) ≃ₗ[k] k × k :=
    { AddEquiv.refl (k × k) with
      map_smul' r m := by
        change (algebraMap k (k × k) r) * (show k × k from m) =
          r • (show k × k from m)
        exact (Algebra.smul_def r (show k × k from m)).symm }
  simp [integerLength, e.length_eq, Module.length_eq_finrank, Module.finrank_prod]

/-- An odd-degree actual complex detects the sign rather than merely total length. -/
theorem twoBranchOddEuler :
    finiteAlgebraFiberEuler k (k × k)
        ((single (ModuleCat (k × k)) (ComplexShape.down ℕ) 1).obj
          (ModuleCat.of (k × k) (k × k)))
        (fun i => (-1) ^ i)
        (finiteHomology_single _ 1 _ (twoBranchFiniteLength k)) = -2 := by
  simpa using twoBranchSingleEuler k 1

end Motivic.MotivicTest.LengthEulerFiniteAlgebra
