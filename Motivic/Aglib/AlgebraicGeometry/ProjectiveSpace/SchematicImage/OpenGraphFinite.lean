/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.GraphClosureFiniteness
/-! # Finiteness from the actual graph closure and an unchanged affine open -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
universe u
namespace AlgebraicGeometry.Scheme
variable {U X Y S : Scheme.{u}} (j : U ⟶ X) (f : X ⟶ S) (g : Y ⟶ S)
  (h : U ⟶ Y) (w : j ≫ f = h ≫ g)
  [IsOpenImmersion j] [QuasiCompact j] [IsSeparated g]

/-- The literal graph's original source is its entire schematic image if that image
has no points outside the original open. No replacement or reduction is performed. -/
theorem graph_toImage_isIso_of_range
    (hno : ∀ x : (pullback.lift j h w).image,
      ((pullback.lift j h w).imageι ≫ pullback.fst f g) x ∈ Set.range j) :
    IsIso (pullback.lift j h w).toImage := by
  let γ := pullback.lift j h w
  have : IsImmersion γ := by
    have : IsImmersion (γ ≫ pullback.fst f g) := by
      simpa [γ] using (inferInstance : IsImmersion j)
    exact IsImmersion.of_comp γ (pullback.fst f g)
  have : QuasiCompact γ := by
    have : QuasiCompact (γ ≫ pullback.fst f g) := by
      simpa [γ] using (inferInstance : QuasiCompact j)
    exact QuasiCompact.of_comp γ (pullback.fst f g)
  let b := IsOpenImmersion.lift j (γ.imageι ≫ pullback.fst f g) (by
    rintro _ ⟨x, rfl⟩
    exact hno x)
  have hb : b ≫ j = γ.imageι ≫ pullback.fst f g := IsOpenImmersion.lift_fac _ _ _
  have hab : γ.toImage ≫ b = 𝟙 U := by
    apply (cancel_mono j).mp
    rw [Category.assoc, hb, ← Category.assoc, Scheme.Hom.toImage_imageι]
    simp [γ]
  have : IsSeparated b := by
    have : IsSeparated (b ≫ j) := by
      rw [hb]
      infer_instance
    exact IsSeparated.of_comp b j
  have : IsProper (γ.toImage ≫ b) := by
    rw [hab]
    infer_instance
  have : IsProper γ.toImage := IsProper.of_comp γ.toImage b
  have : Surjective γ.toImage := surjective_of_isDominant_of_isClosed_range γ.toImage
    γ.toImage.isClosedMap.isClosed_range
  exact (isIso_iff_isOpenImmersion_and_surjective γ.toImage).mpr
    ⟨inferInstance, inferInstance⟩

/-- The original affine coordinate map becomes finite from properness of the same
ambient and absence of its actual graph infinity. -/
theorem isFinite_of_graph_image_range [IsProper f] [IsAffineHom h]
    (hno : ∀ x : (pullback.lift j h w).image,
      ((pullback.lift j h w).imageι ≫ pullback.fst f g) x ∈ Set.range j) : IsFinite h := by
  have := graph_toImage_isIso_of_range j f g h w hno
  have he : (pullback.lift j h w).toImage ≫
      (pullback.lift j h w).imageι ≫ pullback.snd f g = h := by simp
  have : IsProper h := by
    rw [← he]
    infer_instance
  exact (IsFinite.iff_isProper_and_isAffineHom (f := h)).mpr ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme
