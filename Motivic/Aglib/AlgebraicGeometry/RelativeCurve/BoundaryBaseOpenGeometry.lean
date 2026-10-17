module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.LocalAffineBaseFrame
/-! # Simultaneous source and base shrinking retains the whole original finite boundary -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Hom
variable {S X Z : Scheme.{u}} (q : X ⟶ S) (z : Z ⟶ X)
  (U : X.Opens) (V : S.Opens)
  (h : ∀ t : Z, (z ≫ q) t ∈ V → z t ∈ U)

def boundaryBaseSourceOpen : X.Opens := U ⊓ q ⁻¹ᵁ V
abbrev boundaryBaseClosedOpen : Z.Opens := (z ≫ q) ⁻¹ᵁ V

def boundaryBaseSourceProjection : (boundaryBaseSourceOpen q U V).toScheme ⟶ V.toScheme :=
  X.homOfLE (show boundaryBaseSourceOpen q U V ≤ q ⁻¹ᵁ V from inf_le_right) ≫ q ∣_ V

@[reassoc (attr := simp)]
theorem boundaryBaseSourceProjection_ι :
    boundaryBaseSourceProjection q U V ≫ V.ι = (boundaryBaseSourceOpen q U V).ι ≫ q := by
  simp [boundaryBaseSourceProjection]

/-- The unchanged full inverse image of the base open lies in the chosen source open. -/
def boundaryBaseLift : (boundaryBaseClosedOpen q z V).toScheme ⟶
    (boundaryBaseSourceOpen q U V).toScheme :=
  IsOpenImmersion.lift (boundaryBaseSourceOpen q U V).ι
    ((boundaryBaseClosedOpen q z V).ι ≫ z) (by
      rintro _ ⟨t, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact ⟨h t.val t.property, t.property⟩)

@[reassoc (attr := simp)]
theorem boundaryBaseLift_ι :
    boundaryBaseLift q z U V h ≫ (boundaryBaseSourceOpen q U V).ι =
      (boundaryBaseClosedOpen q z V).ι ≫ z := IsOpenImmersion.lift_fac _ _ _

@[reassoc]
theorem boundaryBaseLift_projection :
    boundaryBaseLift q z U V h ≫ boundaryBaseSourceProjection q U V = (z ≫ q) ∣_ V := by
  apply (cancel_mono V.ι).mp
  simp only [Category.assoc, boundaryBaseSourceProjection_ι,
    boundaryBaseLift_ι_assoc, morphismRestrict_ι]

include h in
/-- The square is literally Cartesian, so no nilpotents of the original boundary are lost. -/
theorem boundaryBaseLift_isPullback :
    IsPullback (boundaryBaseLift q z U V h) (boundaryBaseClosedOpen q z V).ι
      (boundaryBaseSourceOpen q U V).ι z := by
  apply IsOpenImmersion.isPullback
  · exact (boundaryBaseLift_ι q z U V h).symm
  · simp only [Scheme.Opens.opensRange_ι]
    ext t
    change (z t ∈ U ∧ (z ≫ q) t ∈ V) ↔ (z ≫ q) t ∈ V
    exact ⟨And.right, fun ht => ⟨h t ht, ht⟩⟩

theorem boundaryBaseLift_finite [IsFinite (z ≫ q)] :
    IsFinite (boundaryBaseLift q z U V h ≫ boundaryBaseSourceProjection q U V) := by
  rw [boundaryBaseLift_projection]
  infer_instance

theorem boundaryBaseSourceProjection_smooth [SmoothOfRelativeDimension 1 q] :
    SmoothOfRelativeDimension 1 (boundaryBaseSourceProjection q U V) := by
  have : SmoothOfRelativeDimension 1 (q ∣_ V) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict q V).flip inferInstance
  dsimp [boundaryBaseSourceProjection]
  exact smoothOfRelativeDimension_comp (n := 0) (m := 1) _ _

/-- Affine source and base opens remain actual affine schemes after this simultaneous shrink. -/
theorem boundaryBaseSourceOpen_affine [IsAffine S] (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) : IsAffineOpen (boundaryBaseSourceOpen q U V) := by
  have : IsAffine U.toScheme := hU
  have ha := (hV.preimage (U.ι ≫ q)).image_of_isOpenImmersion U.ι
  convert ha using 1
  rw [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι]
  rfl
end AlgebraicGeometry.Scheme.Hom
