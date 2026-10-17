module
public import Mathlib.AlgebraicGeometry.Normalization

/-! # No new normalization boundary over an actually finite affine chart

The statement concerns the original normalization and literal open chart.
It rules out vertical boundary components there by finiteness, not by dimension.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.Hom
variable {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]

/-- If the original map is integral over an open chart, every normalization point
over that chart is already in the original source. -/
theorem mem_range_toNormalization_of_integral_chart (U : X.Opens)
    [IsIntegralHom (pullback.snd f U.ι)] (x : f.normalization)
    (hx : f.fromNormalization x ∈ U) : x ∈ Set.range f.toNormalization := by
  let g := (pullback.snd f U.ι).toNormalization ≫ f.normalizationPullback U.ι
  have : IsIso g := by dsimp [g]; infer_instance
  obtain ⟨w, hw, _⟩ := Scheme.exists_preimage_of_isPullback
    (IsPullback.of_hasPullback f.fromNormalization U.ι) x
    ⟨f.fromNormalization x, hx⟩ rfl
  have hg : Function.Surjective g := (inferInstance : Surjective g).surj
  obtain ⟨z, hz⟩ := hg w
  refine ⟨pullback.fst f U.ι z, ?_⟩
  have he := f.toNormalization_normalizationPullback_fst U.ι
  have hpoint := congrArg (fun a => a z) he
  change (pullback.fst f.fromNormalization U.ι) (g z) =
    f.toNormalization (pullback.fst f U.ι z) at hpoint
  rw [hz, hw] at hpoint
  exact hpoint.symm

/-- When the original source is entirely over the integral chart, the full missing
normalization boundary lies exactly over its complement. -/
theorem range_toNormalization_eq_preimage_integral_chart (U : X.Opens)
    [IsIntegralHom (pullback.snd f U.ι)] (hU : f ⁻¹ᵁ U = ⊤) :
    Set.range f.toNormalization = f.fromNormalization ⁻¹' (U : Set X) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change (f.toNormalization ≫ f.fromNormalization) y ∈ U
    rw [f.toNormalization_fromNormalization]
    change y ∈ f ⁻¹ᵁ U
    simp [hU]
  · exact f.mem_range_toNormalization_of_integral_chart U x

end AlgebraicGeometry.Scheme.Hom
