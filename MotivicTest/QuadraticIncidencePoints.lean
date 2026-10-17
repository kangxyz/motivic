/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Motivic.Aglib.RingTheory.Bertini.QuadraticIncidenceParameterMap
import Lean.Util.CollectAxioms

/-! # Original parameter relations hold at every actual bad field point -/
noncomputable section
open Module TensorProduct KaehlerDifferential MvPolynomial
universe u
namespace QuadraticIncidence
variable (k R A K : Type u) [CommRing k] [CommRing R] [CommRing A] [Field K]
  [Algebra k R] [Algebra R A] [Algebra k A] [Algebra R K] [Algebra A K]
  [Algebra k K] [IsScalarTower R A K] [IsScalarTower k A K] [Algebra.Smooth k R]
  {σ : Type u} [Fintype σ]

example
    (g : σ → R) (a : σ → A) (d : ℕ) (w : Fin d → A)
    (p : Fin d → restrictTotalDegree σ K 2)
    (hvalue : ∀ i, eval (fun j => algebraMap R K (g j)) (p i).val =
      eval (algebraMap A K ∘ a) (p i).val)
    (hderiv : ∑ i, algebraMap A K (w i) • residueGeneratorGradient k R K g
      (fun j => eval (fun l => algebraMap R K (g l)) (pderiv j (p i).val)) = 0)
    (f : MvPolynomial (Fin d × Exponent σ) k)
    (hf : parameterMap k R A g a d w f = 0) :
    aeval (fun q => (parameterBasis K σ d).repr p q) f = 0 :=
  parameter_relation_vanishes k R A K g a d w p hvalue hderiv f hf

open Lean in
run_cmd do
  for name in #[``sum_parameterCoefficients_smul, ``sum_parameterCoefficients_eq_zero,
      ``parameterCoefficients_ideal_le_ker, ``pointMap, ``pointMap_coordinates,
      ``parameterMap, ``parameter_relation_vanishes] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual bad-point parameter maps: standard foundations only."

end QuadraticIncidence
