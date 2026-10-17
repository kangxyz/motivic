import Motivic.Aglib.AlgebraicGeometry.SmoothCartierEtaleComparison
import Lean.Util.CollectAxioms

/-! # Original-scheme consumer and axiom audit for smooth Cartier comparison -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace MotivicTest.GeneralSmoothCartierEtaleComparison

theorem original_smooth_cartier_pair
    {k : Type u} [Field k] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (p : X ⟶ Spec (.of k))
    [Smooth p] [Smooth (i ≫ p)]
    (hI : IsLocallyRankOne X (Scheme.Hom.idealModule i)) (z : Z) :
    ∃ U : X.Opens, IsAffineOpen U ∧ i z ∈ U ∧
      ∃ (V : Scheme.{u}) (a : V ⟶ U.toScheme)
        (b : V ⟶ Scheme.Hom.cylinder k ((i ⁻¹ᵁ U).ι ≫ i ≫ p))
        (j : (i ⁻¹ᵁ U).toScheme ⟶ V),
        Etale a ∧ Etale b ∧
        IsPullback j (𝟙 _) a (i ∣_ U) ∧
        IsPullback j (𝟙 _) b
          (Scheme.Hom.cylinderZeroSection k ((i ⁻¹ᵁ U).ι ≫ i ≫ p)) ∧
        IsIso (pullback.snd a (i ∣_ U)) ∧
        IsIso (pullback.snd b
          (Scheme.Hom.cylinderZeroSection k ((i ⁻¹ᵁ U).ι ≫ i ≫ p))) :=
  AlgebraicGeometry.Scheme.exists_smooth_cartier_etale_cylinder_comparison i p hI z

end MotivicTest.GeneralSmoothCartierEtaleComparison

open Lean in
run_cmd do
  let targets := #[
    `MotivicTest.GeneralSmoothCartierEtaleComparison.original_smooth_cartier_pair,
    `AlgebraicGeometry.Scheme.exists_smooth_cartier_etale_cylinder_comparison]
  for name in targets do
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original smooth Cartier pair comparison: standard axioms only."
