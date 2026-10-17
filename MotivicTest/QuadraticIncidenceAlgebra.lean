module
import Motivic.Aglib.RingTheory.Bertini.QuadraticIncidenceAlgebra
import Lean.Util.CollectAxioms

/-! # The literal universal incidence quotient uses the original cotangent module -/
open Module TensorProduct MvPolynomial

example (k R A : Type) [CommRing k] [CommRing R] [CommRing A]
    [Algebra k R] [Algebra R A] [Algebra.Smooth k R]
    {σ : Type} [Fintype σ] (g : σ → R) (a : σ → A) (d : ℕ) (w : Fin d → A) :
    ProjectiveIncidence.universalVector (R := A)
      (QuadraticIncidence.coefficientVector k R A g a d w) = 0 :=
  QuadraticIncidence.universal_equations k R A g a d w

example (R A V : Type) [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Projective R V]
    {N : Type} [Fintype N] (v : N → V) (x : N → A) :
    LinearIncidence.ideal (ProjectiveIncidence.coefficientMatrix (R := R) v) ≤
      RingHom.ker (aeval x).toRingHom ↔ (∑ i, x i ⊗ₜ[R] v i : A ⊗[R] V) = 0 :=
  ProjectiveIncidence.equations_iff_vector_eq_zero v x

open LinearIncidence ProjectiveIncidence QuadraticIncidence in
open Lean in
run_cmd do
  for name in #[``equations_hold, ``adjoin_coordinates_eq_top,
      ``universalVector_eq_zero, ``equations_iff_vector_eq_zero, ``universal_equations] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Literal quadratic incidence algebra: standard foundations only."
