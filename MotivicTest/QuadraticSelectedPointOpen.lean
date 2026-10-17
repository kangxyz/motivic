/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.QuadraticSelectedPointOpen
public import Motivic.Aglib.RingTheory.Bertini.WholeOffDiagonalFiberParameters
public import Lean

/-! # The selected-point and whole off-diagonal conditions use one coefficient tuple -/
public noncomputable section
open Module TensorProduct KaehlerDifferential MvPolynomial QuadraticIncidence
universe u
namespace MotivicTest.QuadraticSelectedPointOpen

/-- No infinite-ground-field assumption or rational-point assumption is used to
produce the selected-point principal open. -/
theorem actual_selected_open (k R L : Type u) [Field k] [CommRing R] [IsDomain R]
    [Field L] [Algebra k R] [Algebra R L] [Algebra k L] [Algebra.Smooth k R]
    {σ : Type u} [Fintype σ] (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k R = (d + 1 : ℕ)) :
    ∃ q : MvPolynomial (Fin d × Exponent σ) k, q ≠ 0 ∧
      ∀ c : Fin d × Exponent σ → k, eval c q ≠ 0 →
        LinearIndependent L (fun i => residueGeneratorGradient k R L g
          (fun j => eval (fun l => algebraMap R L (g l))
            (pderiv j (parameterTuple L σ d (algebraMap k L ∘ c) i).val))) :=
  exists_selectedPoint_open_of_smooth g hg d hd

/-- The actual off-diagonal producer consumes the selected-point polynomial;
there is only one final choice of the original quadratic parameters. -/
theorem one_parameter_tuple (k R B L : Type u) [Field k] [Infinite k]
    [CommRing R] [IsDomain R] [CommRing B] [Field L]
    [Algebra k R] [Algebra k B] [Algebra R B] [IsScalarTower k R B]
    [Module.Finite R B] [Algebra.Smooth k R] [Algebra k L] [Algebra R L]
    {σ : Type u} [Fintype σ] (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (a : σ → B)
    (d : ℕ) (hd : Algebra.trdeg k R = (d + 1 : ℕ)) :
    ∃ c : Fin d × Exponent σ → k,
      GoodOffDiagonalParameters k R B g a d c ∧
        LinearIndependent L (fun i => residueGeneratorGradient k R L g
          (fun j => eval (fun l => algebraMap R L (g l))
            (pderiv j (parameterTuple L σ d (algebraMap k L ∘ c) i).val))) := by
  obtain ⟨q, hq, h⟩ := exists_selectedPoint_open_of_smooth (L := L) g hg d hd
  obtain ⟨c, hc, hoff⟩ := exists_goodOffDiagonalParameters k R B g hg a d hd q hq
  exact ⟨c, hoff, h c hc⟩

open Lean in
run_cmd do
  for name in #[``actual_selected_open, ``one_parameter_tuple,
      ``selectedDerivative_surjective, ``selectedDeterminant_ne_zero,
      ``independent_of_selectedDeterminant, ``exists_ground_open,
      ``exists_selectedPoint_open_of_smooth] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Selected and off-diagonal conditions: standard foundations only."

end MotivicTest.QuadraticSelectedPointOpen
