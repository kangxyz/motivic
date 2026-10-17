/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.AffineLineCoprimeOpenPresentation
public import Mathlib.Algebra.Field.ZMod
public import Lean

/-! # Original affine-line opens and coprime monic equations -/
public noncomputable section
open AlgebraicGeometry Polynomial
open Motivic.AffineLineReducedComplement
universe u
namespace MotivicTest.AffineLineCoprimeOpenPresentation

/-- The consumer retains the original opens, including over finite fields. -/
theorem actual_open_pair (k : Type u) [Field k]
    (U V : (line k).Opens) (hVU : V ≤ U) (hV : (V : Set (line k)).Nonempty) :
    ∃ f g : k[X], f.Monic ∧ g.Monic ∧ IsCoprime f g ∧
      PrimeSpectrum.basicOpen f = U ∧ PrimeSpectrum.basicOpen (f * g) = V :=
  exists_coprime_monic_open_presentation U V hVU hV

/-- A literal characteristic-two instance does not introduce an infinitude hypothesis. -/
example (U V : (line (ZMod 2)).Opens) (hVU : V ≤ U)
    (hV : (V : Set (line (ZMod 2))).Nonempty) :
    ∃ f g : (ZMod 2)[X], f.Monic ∧ g.Monic ∧ IsCoprime f g ∧
      PrimeSpectrum.basicOpen f = U ∧ PrimeSpectrum.basicOpen (f * g) = V :=
  actual_open_pair (ZMod 2) U V hVU hV

/-- The punctured-line example allows g(0)=0: no false unit condition is inserted. -/
theorem punctured_line_pair (k : Type u) [Field k] :
    (1 : k[X]).Monic ∧ (X : k[X]).Monic ∧ IsCoprime (1 : k[X]) X ∧
      PrimeSpectrum.basicOpen (1 : k[X]) = ⊤ ∧
      PrimeSpectrum.basicOpen ((1 : k[X]) * X) = PrimeSpectrum.basicOpen X ∧
      (X : k[X]).eval 0 = 0 := by
  simp [isCoprime_one_left]

open Lean in
run_cmd do
  for name in #[``actual_open_pair, ``punctured_line_pair,
      ``exists_monic_squarefree_presentation, ``exists_coprime_monic_open_presentation] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original nested opens and coprime equations: standard foundations only."

end MotivicTest.AffineLineCoprimeOpenPresentation
