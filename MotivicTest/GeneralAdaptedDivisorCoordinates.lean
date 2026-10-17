import Motivic.Aglib.AlgebraicGeometry.AffineDivisorEtaleComparison
import Motivic.Aglib.AlgebraicGeometry.AffinePrincipalDivisorChart
import Lean.Util.CollectAxioms

/-! # Direct consumer and axiom audit for actual adapted smooth-divisor coordinates -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace MotivicTest.GeneralAdaptedDivisorCoordinates

theorem actual_smooth_divisor_comparison
    (k R : Type u) [Field k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]
    (t : R) (ht : IsRegular t) [Algebra.FormallySmooth k (R ⧸ Ideal.span {t})]
    (p : Ideal R) [p.IsPrime] (htp : t ∈ p) :
    ∃ r ∉ p,
      let B := Localization.Away r
      let D := B ⧸ Ideal.span {algebraMap R B t}
      ∃ (V : Scheme.{u}) (a : V ⟶ Spec (.of B)) (b : V ⟶ Spec (.of (Polynomial D)))
        (j : Spec (.of D) ⟶ V), Etale a ∧ Etale b ∧
        IsPullback j (𝟙 _) a
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap R B t})))) ∧
        IsPullback j (𝟙 _) b (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom 0))) ∧
        IsIso (pullback.snd a
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap R B t}))))) ∧
        IsIso (pullback.snd b (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom 0)))) :=
  AlgebraicGeometry.Scheme.exists_etale_comparison_with_divisor_cylinder k R t ht p htp

end MotivicTest.GeneralAdaptedDivisorCoordinates

open Lean in
run_cmd do
  let targets := #[
    `MotivicTest.GeneralAdaptedDivisorCoordinates.actual_smooth_divisor_comparison,
    `AlgebraicGeometry.Scheme.exists_affine_etale_chart_preserving_principal_divisor,
    `AlgebraicGeometry.Scheme.exists_etale_comparison_with_divisor_cylinder,
    `Algebra.exists_etale_polynomial_chart_preserving_regular_generator]
  for name in targets do
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual smooth-divisor chart and comparison: standard axioms only."
