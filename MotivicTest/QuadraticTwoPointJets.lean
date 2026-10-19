module
import Motivic.Aglib.RingTheory.Bertini.QuadraticJetParameters
import Lean.Util.CollectAxioms

/-! # Direct quadratic jet consumers and foundation audit -/
open _root_.MvPolynomial

example (K : Type) [Field K] {σ : Type} [Finite σ]
    (a b : σ → K) (hab : a ≠ b) (c : K) (v : σ → K) :
    ∃ f : MvPolynomial σ K, f.totalDegree ≤ 2 ∧ eval b f - eval a f = c ∧
      ∀ i, eval b (pderiv i f) = v i :=
  exists_quadratic_value_difference_jet a b hab c v

example (K : Type) [Field K] {σ : Type} [Finite σ]
    (a b : σ → K) (hab : a ≠ b) :
    Function.Surjective (quadraticJetParameters a b) :=
  quadraticJetParameters_surjective a b hab

example (K : Type) [Field K] {σ : Type} [Finite σ] :
    Module.Finite K (restrictTotalDegree σ K 2) := inferInstance

example (R : Type) [CommRing R] {σ : Type} [Finite σ]
    (a b : σ → R) (j : σ) (e : R) (he : e * (b j - a j) = 1) :
    Function.Surjective (quadraticJetParameters a b) :=
  quadraticJetParameters_surjective_of_inverse a b j e he

open Lean in
run_cmd do
  for name in #[``exists_quadratic_two_point_jet,
      ``exists_quadratic_value_difference_jet, ``quadraticJetParameters_surjective,
      ``quadraticJetParameters_surjective_of_inverse] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Quadratic whole-fiber incidence input: standard foundations only."
