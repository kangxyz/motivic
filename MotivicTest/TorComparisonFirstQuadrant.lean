/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.FlatComplexTensorSingle

/-! Consumers for actual first-quadrant acyclicity and the ordinary Tor target. -/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory HomologicalComplex

universe u

namespace Motivic.MotivicTest.TorComparisonFirstQuadrant

variable {R : Type u} [CommRing R]

/-- Arbitrary unbounded first-quadrant exact rows give an exact actual total. -/
theorem totalExact
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (hK : ∀ q, (K.flip.X q).Acyclic) (n : ℕ) :
    (K.total (ComplexShape.down ℕ)).ExactAt n :=
  _root_.ModuleCat.TorComparison.firstQuadrant_total_acyclic K hK n

/-- The proof supplies an actual primitive for every genuine total cycle. -/
theorem totalBoundary
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (hK : ∀ q, (K.flip.X q).Acyclic) (n : ℕ)
    (x : (K.total (ComplexShape.down ℕ)).X n)
    (hx : (K.total (ComplexShape.down ℕ)).d n (n - 1) x = 0) :
    ∃ y : (K.total (ComplexShape.down ℕ)).X (n + 1),
      (K.total (ComplexShape.down ℕ)).d (n + 1) n y = x :=
  _root_.ModuleCat.TorComparison.firstQuadrant_boundary_of_below K hK (n + 1) n (le_refl _) x hx
    (by rw [_root_.ModuleCat.TorComparison.firstQuadrantBelow_succ_self]; rfl)

/-- Degreewise flatness suffices even for two unbounded nonnegative complexes. -/
theorem flatTensorExact (A G : ChainComplex (ModuleCat.{u} R) ℕ)
    (hA : A.Acyclic) [∀ q, Module.Flat R (G.X q)] (n : ℕ) :
    (mapBifunctor A G (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)).ExactAt n :=
  _root_.ModuleCat.TorComparison.flatComplexTensor_acyclic A G hA n

/-- The resolved module can be arbitrary and need not be flat. -/
theorem resolutionTensorExact (A : ChainComplex (ModuleCat.{u} R) ℕ)
    (hA : A.Acyclic) {N : ModuleCat.{u} R} (P : ProjectiveResolution N) (n : ℕ) :
    (mapBifunctor A P.complex (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)).ExactAt n :=
  _root_.ModuleCat.TorComparison.resolutionTensor_acyclic A hA P n

/-- The target comparison is an actual chain isomorphism. -/
noncomputable def ordinaryTensorComplex (M : ModuleCat.{u} R)
    (G : ChainComplex (ModuleCat.{u} R) ℕ) :
    mapBifunctor ((ChainComplex.single₀ (ModuleCat R)).obj M) G
        (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ) ≅
      ((tensorLeft M).mapHomologicalComplex (ComplexShape.down ℕ)).obj G :=
  _root_.ModuleCat.TorComparison.flatComplexTensorSingleIso M G

/-- The single-factor total computes mathlib's literal one-sided Tor in every degree. -/
noncomputable def actualOneSidedTor (M N : ModuleCat.{u} R)
    (P : ProjectiveResolution N) (n : ℕ) :
    (mapBifunctor ((ChainComplex.single₀ (ModuleCat R)).obj M) P.complex
        (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)).homology n ≅
      (((Tor (ModuleCat R) n).obj M).obj N) :=
  _root_.ModuleCat.TorComparison.flatComplexTensorSingleTorIso M P n

end Motivic.MotivicTest.TorComparisonFirstQuadrant
