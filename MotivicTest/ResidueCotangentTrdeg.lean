module
public import Motivic.Aglib.RingTheory.Etale.ResidueCotangentTrdeg
public import Motivic.Aglib.RingTheory.AlgebraicIndependent.QuotientTrdeg
public import Lean.Util.CollectAxioms

/-! # Actual cotangent-rank to ambient and closed-quotient dimension tests -/
@[expose] public noncomputable section

open Module TensorProduct KaehlerDifferential

universe u

namespace Motivic.MotivicTest.ResidueCotangentTrdeg

/-- Quasi-finiteness gives actual algebraicity, with no chosen finite extension. -/
theorem quasiFinite_domain_algebraic
    (A B : Type*) [CommRing A] [CommRing B] [IsDomain B] [Algebra A B]
    [Algebra.QuasiFinite A B] : Algebra.IsAlgebraic A B :=
  Algebra.QuasiFinite.isAlgebraic_of_isDomain A B

/-- The chart theorem applies over any field, including finite fields. -/
theorem polynomial_dimension_from_etale_identity (k : Type u) [Field k] (n : ℕ) :
    Algebra.trdeg k (MvPolynomial (Fin n) k) = n :=
  Algebra.trdeg_eq_of_etale_polynomial_map (AlgHom.id k _)
    (RingHom.Etale.of_bijective Function.bijective_id)

/-- A specified actual étale map after a nonzero localization supplies the bound. -/
theorem localized_polynomial_map_bounds_original_domain
    {k R : Type u} [Field k] [CommRing R] [IsDomain R] [Algebra k R]
    {n : ℕ} (f : MvPolynomial (Fin n) k →ₐ[k] R) {r : R} (hr : r ≠ 0)
    (hf : ((algebraMap R (Localization.Away r)).comp f.toRingHom).Etale) :
    Algebra.trdeg k R ≤ n :=
  Algebra.trdeg_le_of_etale_localized_polynomial_map f hr hf

/-- One actual prime, rather than a possibly empty selected family, gives a bound. -/
theorem actual_residue_rank_bounds_ambient
    (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R]
    [Algebra.Smooth k R] (p : Ideal R) [p.IsPrime] {n : ℕ}
    (hn : Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime p))
      (IsLocalRing.ResidueField (Localization.AtPrime p) ⊗[R] Ω[R⁄k]) = n) :
    Algebra.trdeg k R ≤ n :=
  Algebra.trdeg_le_of_residue_cotangent_finrank k R p hn

/-- The actual rank derives the whole nonreduced closed-quotient bound;
neither an ambient nor a quotient transcendence bound is assumed. -/
theorem actual_residue_rank_bounds_whole_closed_quotient
    (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R]
    [Algebra.Smooth k R] (p : Ideal R) [p.IsPrime]
    (I : Ideal R) (hI : I ≠ ⊥) {d : ℕ}
    (hd : Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime p))
      (IsLocalRing.ResidueField (Localization.AtPrime p) ⊗[R] Ω[R⁄k]) = d + 1) :
    Algebra.trdeg k (R ⧸ I) ≤ d := by
  apply I.trdeg_quotient_le_of_ne_bot hI
  simpa only [Nat.cast_add, Nat.cast_one] using
    Algebra.trdeg_le_of_residue_cotangent_finrank k R p hd

open Lean in
run_cmd do
  for name in #[``Algebra.QuasiFinite.isAlgebraic_of_isDomain,
      ``Algebra.trdeg_eq_of_etale_mvPolynomial,
      ``Algebra.trdeg_eq_of_etale_polynomial_map,
      ``Algebra.trdeg_le_of_etale_localized_polynomial_map,
      ``Algebra.trdeg_le_of_residue_differential_basis,
      ``Algebra.trdeg_le_of_residue_cotangent_finrank,
      ``quasiFinite_domain_algebraic, ``polynomial_dimension_from_etale_identity,
      ``localized_polynomial_map_bounds_original_domain,
      ``actual_residue_rank_bounds_ambient,
      ``actual_residue_rank_bounds_whole_closed_quotient] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Residue cotangent transcendence-degree audit passed: standard foundations only."

end Motivic.MotivicTest.ResidueCotangentTrdeg
