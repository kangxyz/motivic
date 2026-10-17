module
import Motivic.Aglib.RingTheory.Etale.FiniteBadLocusProjection
import Lean.Util.CollectAxioms

/-! # Actual same-coordinate finite/smooth bad-locus supplier and foundation audit -/
open Module TensorProduct KaehlerDifferential MvPolynomial

example (k R : Type) [Field k] [Infinite k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.Smooth k R] (I : Ideal R) (hI : I ≠ ⊥) (d : ℕ)
    (hR : Algebra.trdeg k R ≤ d + 1)
    (p : Ideal R) [p.IsPrime]
    (hd : Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime p))
      (IsLocalRing.ResidueField (Localization.AtPrime p) ⊗[R] Ω[R⁄k]) = d + 1) :
    ∃ ψ : MvPolynomial (Fin (d + 1)) k →ₐ[k] R, ψ.Finite ∧
      ((Ideal.Quotient.mkₐ k I).comp (ψ.comp (MvPolynomial.rename Fin.succ))).Finite ∧
      ∃ r ∉ p, ((algebraMap R (Localization.Away r)).comp ψ.toRingHom).Etale ∧
        RingHom.IsStandardSmoothOfRelativeDimension 1
          ((algebraMap R (Localization.Away r)).comp
            (ψ.comp (MvPolynomial.rename Fin.succ)).toRingHom) := by
  obtain ⟨ψ, hfin, hclosed, hh⟩ := Algebra.exists_finite_bad_locus_curve_projection
    k R I hI d hR (fun _ : Unit => p) (fun _ => hd)
  exact ⟨ψ, hfin, hclosed, hh ()⟩

open ParameterizedNoetherNormalization
open Lean in
run_cmd do
  for name in #[``Algebra.exists_finite_bad_locus_curve_projection,
      ``KaehlerDifferential.exists_finite_ambient_and_closed_projection,
      ``exists_iterated_finite_projection_preserving_differential_minors] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual finite projection audit passed: standard foundations only."
