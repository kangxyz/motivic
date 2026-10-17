import Motivic.Aglib.AlgebraicGeometry.SmoothCartierEtaleComparisonOverBase
import Lean.Util.CollectAxioms

/-! # Actual smooth Cartier comparison over its field with small-site maps -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace MotivicTest.SmoothCartierOverBase

theorem original_pair_over_field_with_small_site_maps
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
          (Scheme.Hom.cylinderZeroSection k ((i ⁻¹ᵁ U).ι ≫ i ≫ p))) ∧
        a ≫ U.ι ≫ p = b ≫ pullback.snd _ _ ≫ (i ⁻¹ᵁ U).ι ≫ i ≫ p ∧
        IsSeparated a ∧ IsSeparated b ∧ QuasiCompact a ∧ QuasiCompact b :=
  AlgebraicGeometry.Scheme.exists_smooth_cartier_etale_cylinder_comparison_over_base i p hI z

end MotivicTest.SmoothCartierOverBase

open Lean in
run_cmd do
  let targets := #[
    `MotivicTest.SmoothCartierOverBase.original_pair_over_field_with_small_site_maps,
    `AlgebraicGeometry.Scheme.exists_smooth_cartier_etale_cylinder_comparison_over_base]
  for name in targets do
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original Cartier comparison over its field: standard axioms only."
