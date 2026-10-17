module

public import Motivic.Aglib.RingTheory.NormalMonicFactorization
public import Lean.Util.CollectAxioms

/-! # Direct audit of normal-domain monic prime factorization -/

@[expose] public noncomputable section

open Polynomial

example {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (p : R[X]) (hp : p.Monic) (hu : IsUnit (p.coeff 0)) :
    ∃ l : List R[X], l.prod = p ∧
      ∀ q ∈ l, q.Monic ∧ Prime q ∧ IsUnit (q.coeff 0) :=
  exists_list_monic_prime_factors_of_normal p hp hu

open Lean in
run_cmd do
  for name in #[``Polynomial.exists_monic_factor_descent,
      ``Polynomial.Monic.prime_of_prime_map_fractionRing,
      ``Polynomial.exists_monic_prime_factor_of_normal,
      ``Polynomial.exists_list_monic_prime_factors_of_normal] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Normal-domain monic prime factorization uses only standard Lean foundations."
