/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.TorComparison.ConeAugmentationCriterion
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution

/-! Consumers of the actual nonnegative module homotopy-cofiber criterion. -/

@[expose] public section

open CategoryTheory HomologicalComplex

universe u

namespace Motivic.MotivicTest.TorComparisonConeAugmentationCriterion

variable {R : Type u} [CommRing R]
  {A B : ChainComplex (ModuleCat.{u} R) ℕ} (f : A ⟶ B)

/-- The criterion applies to arbitrary nonnegative complexes, without term flatness. -/
theorem actualConeCriterion : (homotopyCofiber f).Acyclic ↔ QuasiIso f :=
  TorComparison.homotopyCofiber_acyclic_iff_quasiIso f

/-- The quasi-isomorphism conclusion includes degree zero. -/
theorem degreeZero (h : (homotopyCofiber f).Acyclic) : QuasiIsoAt f 0 := by
  have := TorComparison.quasiIso_of_homotopyCofiber_acyclic f h
  infer_instance

/-- The cofiber of the literal augmentation of any genuine resolution is acyclic. -/
theorem resolutionAugmentation {M : ModuleCat.{u} R} (P : ProjectiveResolution M) :
    (homotopyCofiber P.π).Acyclic :=
  TorComparison.homotopyCofiber_acyclic_of_quasiIso P.π

/-- The source-coordinate sign is the negative of the actual source differential. -/
theorem sourceDifferentialSign (n : ℕ) (x : (homotopyCofiber f).X (n + 2)) :
    homotopyCofiber.fstX f (n + 1) n (TorComparison.cone_rel n)
        ((homotopyCofiber f).d (n + 2) (n + 1) x) =
      -A.d (n + 1) n
        (homotopyCofiber.fstX f (n + 2) (n + 1) (TorComparison.cone_rel (n + 1)) x) :=
  TorComparison.cone_d_fst f n x

/-- Target cycles lift only modulo boundaries, exactly as required by homology. -/
theorem liftedModuloBoundaries (h : (homotopyCofiber f).Acyclic) (n : ℕ)
    (y : B.X n) (hy : B.d n ((ComplexShape.down ℕ).next n) y = 0) :
    ∃ x : A.X n, ∃ z : B.X (n + 1),
      A.d n ((ComplexShape.down ℕ).next n) x = 0 ∧
        f.f n x - y = B.d (n + 1) n z :=
  TorComparison.cone_liftCycles f h n y hy

end Motivic.MotivicTest.TorComparisonConeAugmentationCriterion
